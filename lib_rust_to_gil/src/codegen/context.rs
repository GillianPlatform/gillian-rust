use rustc_borrowck::borrow_set::BorrowSet;
use rustc_borrowck::consumers::RegionInferenceContext;
use rustc_middle::mir::visit::PlaceContext;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::ty::PolyFnSig;
use rustc_middle::ty::RegionVid;
use rustc_span::def_id::DefId;
use std::collections::HashMap;
use std::collections::HashSet;

use super::names::{gil_temp_from_id, temp_name_from_local};
use super::typ_encoding::lifetime_param_name;
use crate::codegen::function_call::poor_man_unification;
use crate::codegen::typ_encoding::region_name;
use crate::prelude::*;

pub struct GilCtxt<'tcx, 'body> {
    locals_in_memory: HashSet<Local>,
    gil_body: ProcBody,
    gil_temp_counter: usize,
    switch_label_counter: usize,
    next_label: Option<String>,
    mir: &'body Body<'tcx>,
    pub region_info: RegionInfo<'body, 'tcx>,
    pub(crate) global_env: &'body mut GlobalEnv<'tcx>,
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
            .unwrap_or_else(|| lifetime_param_name(&repr.as_u32().to_string()) )
    }
}

fn region_info<'body, 'tcx>(
    regioncx: &'body RegionInferenceContext<'tcx>,
    borrows: &'body BorrowSet<'tcx>,
    sig: PolyFnSig<'tcx>,
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

    let mut tbl = HashMap::new();

    for (sig_in, arg_ty) in sig
        .skip_binder()
        .inputs()
        .iter()
        .zip(local_decls.iter().skip(1))
    {
        // let arg_ty = arg.node.ty(self.mir(), self.tcx());
        poor_man_unification(&mut tbl, *sig_in, arg_ty.ty).unwrap();
    }

    // Build a name for each representative
    let mut names = HashMap::new();
    for (name, vid) in tbl {
        let vid = vid.as_var();
        let vid = reborrows.get(&vid).unwrap_or(&vid);
        // if let Some(name) = name.get_name() {
        let scc = regioncx.constraint_sccs().scc(*vid);
        let repr = reprs[&scc.as_u32()];
        // eprintln!("{name:?} : {repr:?}");
        names.insert(repr, region_name(name));
        // }
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
    ) -> Self {
        let mir = body;

        let sig = global_env.tcx().fn_sig(body.source.def_id()).skip_binder();

        let region_info = region_info(
            regioncx,
            borrow_set,
            sig,
            &body.local_decls,
            global_env.tcx(),
        );
        GilCtxt {
            locals_in_memory: locals_in_memory_for_mir(&mir),
            gil_temp_counter: 0,
            switch_label_counter: 0,
            gil_body: ProcBody::default(),
            next_label: None,
            mir,
            region_info,
            global_env,
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
        &self.mir
    }

    pub fn _location(&self, scope: &SourceScope) {
        let _source = self.mir().source_scopes.get(*scope);
    }

    fn original_name_from_local(&self, local: Local) -> Option<String> {
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
