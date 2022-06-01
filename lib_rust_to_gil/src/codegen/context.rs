use rustc_middle::mir::visit::PlaceContext;
use rustc_middle::mir::visit::Visitor;
use rustc_span::def_id::DefId;
use std::collections::HashSet;

use super::names::{gil_temp_from_id, temp_name_from_local};
use crate::prelude::*;

pub struct GilCtxt<'tcx, 'body> {
    locals_in_memory: HashSet<Local>,
    did: DefId,
    pub(crate) tcx: TyCtxt<'tcx>,
    gil_body: ProcBody,
    gil_temp_counter: usize,
    switch_label_counter: usize,
    next_label: Option<String>,
    mir: &'body Body<'tcx>,
    pub(crate) global_env: &'body mut GlobalEnv<'tcx>,
}

impl<'tcx, 'body> CanFatal for GilCtxt<'tcx, 'body> {
    fn fatal(&self, str: &str) -> ! {
        self.tcx.sess.fatal(str)
    }
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn new(
        did: DefId,
        mir: &'body Body<'tcx>,
        ty_ctxt: TyCtxt<'tcx>,
        global_env: &'body mut GlobalEnv<'tcx>,
    ) -> Self {
        GilCtxt {
            did,
            tcx: ty_ctxt,
            locals_in_memory: locals_in_memory_for_mir(mir),
            gil_temp_counter: 0,
            switch_label_counter: 0,
            gil_body: ProcBody::default(),
            next_label: None,
            mir,
            global_env,
        }
    }

    pub fn local_is_in_store(&self, local: &Local) -> bool {
        !self.locals_in_memory.contains(local)
    }

    pub fn place_in_store(&self, place: &Place<'tcx>) -> Option<String> {
        if self.local_is_in_store(&place.local) {
            Some(self.name_from_local(&place.local))
        } else {
            None
        }
    }

    pub fn body_did(&self) -> DefId {
        self.did
    }

    pub fn mir(&self) -> &'body Body<'tcx> {
        self.mir
    }

    pub fn _location(&self, scope: &SourceScope) {
        let _source = self.mir().source_scopes.get(*scope);
    }

    fn original_name_from_local(&self, local: &Local) -> Option<String> {
        self.mir()
            .var_debug_info
            .iter()
            .find_map(|debug_info| match debug_info.value {
                VarDebugInfoContents::Place(place)
                    if place.local == *local && place.projection.is_empty() =>
                {
                    Some(debug_info.name.to_string())
                }
                _ => None,
            })
    }

    pub fn name_from_local(&self, local: &Local) -> String {
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
        // I don't know how to perform downcasting on values in store
        if !place.projection.is_empty() {
            self.0.insert(place.local);
        }
        self.super_place(place, ctx, location);
    }
}
