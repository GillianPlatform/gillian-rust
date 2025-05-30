use crate::location_table::LocationTable;
use crate::signature::anonymous_param_symbol;
use indexmap::IndexMap;
use rustc_borrowck::borrow_set::BorrowSet;
use rustc_borrowck::consumers::PoloniusOutput;
use rustc_borrowck::consumers::RegionInferenceContext;
use rustc_hir::def::DefKind;
use rustc_middle::mir::visit::PlaceContext;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::ty::PolyFnSig;
use rustc_middle::ty::RegionVid;
use rustc_span::def_id::DefId;
use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use super::names::{gil_temp_from_id, temp_name_from_local};
use super::typ_encoding::lifetime_param_name;
use crate::codegen::function_call::poor_man_unification;
use crate::codegen::typ_encoding::region_name;
use crate::prelude::*;

pub struct GilCtxt<'tcx, 'body> {
    /// The set of locals which are used to interact with the heap.
    /// These locals will require specific modeling in Gillian, so we distinguish them
    locals_in_memory: HashSet<Local>,
    gil_body: ProcBody,
    gil_temp_counter: usize,
    switch_label_counter: usize,
    next_label: Option<String>,
    mir: &'body Body<'tcx>,
    pub region_info: RegionInfo<'body, 'tcx>,
    #[allow(dead_code)]
    pub polonius: Rc<PoloniusOutput>,
    #[allow(dead_code)]
    pub location_table: LocationTable,
    pub(crate) global_env: &'body mut GlobalEnv<'tcx>,
    pub(super) activated_borrows: HashSet<RegionVid>,
    anon_map: HashMap<Local, String>,
}

impl<'tcx, 'body> HasTyCtxt<'tcx> for GilCtxt<'tcx, 'body> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.global_env.tcx()
    }
}

impl<'tcx, 'body> HasDefId for GilCtxt<'tcx, 'body> {
    fn did(&self) -> DefId {
        self.mir.source.def_id()
    }
}

impl<'tcx, 'body> HasGlobalEnv<'tcx> for GilCtxt<'tcx, 'body> {
    fn global_env_mut(&mut self) -> &mut GlobalEnv<'tcx> {
        self.global_env
    }

    fn global_env(&self) -> &GlobalEnv<'tcx> {
        self.global_env
    }
}

impl<'tcx> TypeEncoder<'tcx> for GilCtxt<'tcx, '_> {}

pub struct RegionInfo<'body, 'tcx> {
    /// Identifies regions which are simple reborrows of another region.
    reborrows: HashMap<RegionVid, RegionVid>,
    /// Designates a representative for each region cycle, prefering universal regions over others.
    scc_reprs: HashMap<u32, RegionVid>,
    /// Holds a name for each universal or user-named region
    region_names: HashMap<RegionVid, String>,
    /// Context for queries
    regioncx: &'body RegionInferenceContext<'tcx>,
}

impl RegionInfo<'_, '_> {
    pub fn name_region(&self, vid: RegionVid) -> String {
        // Strip reborrows from this region
        let unrebor = self.reborrows.get(&vid).copied().unwrap_or(vid);
        // Now look up the representative
        let scc = self.regioncx.constraint_sccs().scc(unrebor);
        let repr = self.scc_reprs[&scc.as_u32()];
        self.region_names
            .get(&repr)
            .map(|s| s.to_string())
            .unwrap_or_else(|| lifetime_param_name(&repr.as_u32().to_string()))
    }
}

fn region_info<'body, 'tcx>(
    regioncx: &'body RegionInferenceContext<'tcx>,
    borrows: &'body BorrowSet<'tcx>,
    sig: Option<PolyFnSig<'tcx>>, // None for AssocConst
    local_decls: &'body LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> RegionInfo<'body, 'tcx> {
    // Calculate a representative for each region scc. Choosing the minimum prefers universal regions over placeholders
    let mut reprs: HashMap<u32, _> = HashMap::new();

    // Identify reborrows and produce a mapping erasing their lifetimes.
    let reborrows = identify_reborrows(borrows, local_decls, tcx);

    for (reg, orig) in &reborrows {
        assert!(regioncx.eval_outlives(*orig, *reg));
        assert!(!reborrows.contains_key(orig));
    }

    for (reg, scc) in regioncx.constraint_sccs().scc_indices().iter_enumerated() {
        reprs
            .entry(scc.as_u32())
            .and_modify(|pre: &mut RegionVid| *pre = (*pre).min(reg))
            .or_insert(reg);
    }

    let mut tbl = IndexMap::new();

    if let Some(sig) = sig {
        for (sig_in, arg_ty) in sig
            .skip_binder()
            .inputs()
            .iter()
            .zip(local_decls.iter().skip(1))
        {
            // let arg_ty = arg.node.ty(self.mir(), self.tcx());
            poor_man_unification(&mut tbl, *sig_in, arg_ty.ty).unwrap();
        }
    }

    // Build a name for each representative
    let mut names = HashMap::new();
    use itertools::Itertools;
    for (ix, (name, vids)) in tbl.into_iter().enumerate() {
        for (v, w) in vids.iter().tuple_windows() {
            assert!(regioncx.eval_equal(v.as_var(), w.as_var()));
        }

        let vid = vids.first().unwrap().as_var();
        let vid = reborrows.get(&vid).unwrap_or(&vid);
        let scc = regioncx.constraint_sccs().scc(*vid);
        let repr = reprs[&scc.as_u32()];
        names.insert(
            repr,
            region_name(name).unwrap_or_else(|| lifetime_param_name(&ix.to_string())),
        );
    }

    RegionInfo {
        reborrows,
        scc_reprs: reprs,
        region_names: names,
        regioncx,
    }
}

/// Identifies reborrows in the borrow set, that is borrows of the form `&mut * P`.
/// For each of these borrows we produce an additional set of equalities combining their lifetimes into one.
fn identify_reborrows<'tcx>(
    x: &BorrowSet<'tcx>,
    locals: &LocalDecls<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> HashMap<RegionVid, RegionVid> {
    let mut reborrow_lft = HashMap::new();
    for (_, data) in x.location_map.iter() {
        let borrowed = data.borrowed_place;

        let Some(last) = borrowed.iter_projections().last() else {
            continue;
        };

        let is_reborrow = last.1 == ProjectionElem::Deref;

        let ty = last.0.ty(locals, tcx).ty;

        let TyKind::Ref(region, _, _) = ty.kind() else {
            continue;
        };
        let tgt_ty = data.assigned_place.ty(locals, tcx);
        let TyKind::Ref(tgt_reg, _, _) = tgt_ty.ty.kind() else {
            continue;
        };

        let region_vid = region.as_var();
        let subst_region = *reborrow_lft.get(&region_vid).unwrap_or(&region_vid);
        if is_reborrow {
            reborrow_lft.insert(tgt_reg.as_var(), subst_region);
            reborrow_lft.insert(data.region, subst_region);
        }
    }

    reborrow_lft
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn new(
        global_env: &'body mut GlobalEnv<'tcx>,
        body: &'body Body<'tcx>,
        borrow_set: &'body BorrowSet<'tcx>,
        regioncx: &'body RegionInferenceContext<'tcx>,
        polonius: Rc<PoloniusOutput>,
        location_table: LocationTable,
    ) -> Self {
        let mir = body;

        let sig = if let DefKind::AssocConst = global_env.tcx().def_kind(body.source.def_id()) {
            None
        } else {
            Some(global_env.tcx().fn_sig(body.source.def_id()).skip_binder())
        };

        let region_info = region_info(
            regioncx,
            borrow_set,
            sig,
            &body.local_decls,
            global_env.tcx(),
        );

        let anon_map: HashMap<Local, String> = global_env
            .tcx()
            .fn_arg_names(mir.source.def_id())
            .iter()
            .enumerate()
            .filter_map(|(idx, ident)| {
                if ident.name.as_str().is_empty() {
                    Some((
                        Local::from_u32((idx as u32) + 1),
                        anonymous_param_symbol(idx).to_string(),
                    ))
                } else {
                    None
                }
            })
            .collect();

        GilCtxt {
            locals_in_memory: locals_in_memory_for_mir(mir),
            gil_temp_counter: 0,
            switch_label_counter: 0,
            gil_body: ProcBody::default(),
            next_label: None,
            mir,
            region_info,
            global_env,
            polonius,
            location_table,
            anon_map,
            activated_borrows: HashSet::default(),
        }
    }

    pub fn prophecies_enabled(&self) -> bool {
        self.global_env.config.prophecies
    }

    pub fn local_is_in_store(&self, local: Local) -> bool {
        !self.locals_in_memory.contains(&local)
    }

    pub fn place_in_store(&self, place: Place<'tcx>) -> Option<String> {
        if self.local_is_in_store(place.local) {
            Some(self.name_from_local(place.local))
        } else {
            None
        }
    }

    pub fn mir(&self) -> &'body Body<'tcx> {
        self.mir
    }

    pub fn _location(&self, scope: &SourceScope) {
        let _source = self.mir().source_scopes.get(*scope);
    }

    // Retrieves the "original" name of a local.
    // We support two cases: if the input was a single variable defined by the user, then the
    // `var_debug_info` should contain the variable name.
    // Otherwise, there is the case where the input was a user pattern (e.g. `fn f((a, b): (i32, i32)) {...}`)
    // in which case the compiler assigns a single identifier, to which we give a name through `anonymous_param_symbol`.
    // At creation of the GilCtxt, we initialize an `anon_map` which keeps track of anonymous names, and we retrieve the proper name there.
    pub fn original_name_from_local(&self, local: Local) -> Option<String> {
        self.anon_map.get(&local).cloned().or_else(|| {
            self.mir()
                .var_debug_info
                .iter()
                .find_map(|debug_info| match debug_info.value {
                    VarDebugInfoContents::Place(place)
                        if place.local == local && place.projection.is_empty() =>
                    {
                        Some(debug_info.name.to_string())
                    }
                    _ => None,
                })
        })
    }

    pub fn name_from_local(&self, local: Local) -> String {
        temp_name_from_local(local) + &self.original_name_from_local(local).unwrap_or_default()
    }

    pub fn temp_var(&mut self) -> String {
        let current = self.gil_temp_counter;
        self.gil_temp_counter += 1;
        gil_temp_from_id(current)
    }

    pub fn switch_label(&mut self) -> String {
        let current = self.switch_label_counter;
        self.switch_label_counter += 1;
        format!("{}{}", names::SWITCH_LABEL, current)
    }

    pub fn push_label(&mut self, label: String) {
        self.next_label = Some(label);
    }

    fn next_label(&mut self) -> Option<String> {
        std::mem::take(&mut self.next_label)
    }

    pub fn push_cmd(&mut self, cmd: Cmd) {
        let label = self.next_label();
        self.gil_body.push_cmd(cmd, label);
        self.next_label = None;
    }

    pub fn make_proc(self, name: String, args: Vec<String>) -> Proc {
        // Get the body and make it fit first
        let mut items: Vec<ProcBodyItem> = self.gil_body.into();
        items.shrink_to_fit();
        Proc::new(name, args, items)
    }
}

fn locals_in_memory_for_mir(body: &Body) -> HashSet<Local> {
    let mut visitor = ReferencedLocalsVisitor::default();
    visitor.visit_body(body);
    visitor.into_hashset()
}

// Determines the set of locals is used to access the heap: as the base of a borrow, addr_of or discriminant operation.
#[derive(Default)]
struct ReferencedLocalsVisitor(HashSet<Local>);

impl ReferencedLocalsVisitor {
    pub fn into_hashset(self) -> HashSet<Local> {
        self.0
    }
}

impl<'tcx> Visitor<'tcx> for ReferencedLocalsVisitor {
    fn visit_rvalue(&mut self, rvalue: &Rvalue, loc: Location) {
        if let Rvalue::Ref(_, _, place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place) = rvalue
        {
            self.0.insert(place.local);
        }
        self.super_rvalue(rvalue, loc);
    }

    fn visit_place(&mut self, place: &Place<'tcx>, ctx: PlaceContext, location: Location) {
        if !place.projection.is_empty() {
            self.0.insert(place.local);
        }
        self.super_place(place, ctx, location);
    }
}
