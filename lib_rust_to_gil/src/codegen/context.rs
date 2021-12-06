use std::collections::HashSet;

use rustc_middle::mir::visit::{PlaceContext, Visitor};

use super::names::{gil_temp_from_id, temp_name_from_local};
use crate::prelude::*;

pub struct GilCtxt<'tcx, 'body> {
    pub(crate) instance: Instance<'tcx>,
    pub(crate) ty_ctxt: TyCtxt<'tcx>,
    gil_body: ProcBody,
    gil_temp_counter: usize,
    switch_label_counter: usize,
    next_label: Option<String>,
    mir: &'tcx Body<'tcx>,
    locals_in_memory: HashSet<Local>,
    pub(crate) global_env: &'body mut GlobalEnv<'tcx>,
}

impl<'tcx, 'body> CanFatal for GilCtxt<'tcx, 'body> {
    fn fatal(&self, str: &str) -> ! {
        self.ty_ctxt.sess.fatal(str);
    }
}

fn locals_in_memory_for_mir(body: &Body) -> HashSet<Local> {
    let mut visitor = ReferencedLocalsVisitor::default();
    visitor.visit_body(body);
    visitor.into_hashset()
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn new(
        instance: Instance<'tcx>,
        ty_ctxt: TyCtxt<'tcx>,
        global_env: &'body mut GlobalEnv<'tcx>,
    ) -> Self {
        let mir = ty_ctxt.instance_mir(instance.def);
        let locals_in_memory = locals_in_memory_for_mir(mir);
        GilCtxt {
            instance,
            ty_ctxt,
            gil_temp_counter: 0,
            switch_label_counter: 0,
            gil_body: ProcBody::default(),
            next_label: None,
            mir,
            locals_in_memory,
            global_env,
        }
    }
    pub fn mir(&self) -> &'tcx Body<'tcx> {
        self.mir
    }

    pub fn _location(&self, scope: &SourceScope) {
        let _source = self.mir().source_scopes.get(*scope);
    }

    pub fn local_is_in_memory(&self, local: &Local) -> bool {
        self.locals_in_memory.contains(local)
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

    pub fn sanitized_original_name_from_local(&self, local: &Local) -> Option<String> {
        self.original_name_from_local(local)
            .map(names::sanitize_name)
    }

    pub fn name_from_local(&self, local: &Local) -> String {
        match self.sanitized_original_name_from_local(local) {
            Some(name) => name,
            None => temp_name_from_local(local),
        }
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
        log::debug!("{}", cmd);
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

#[derive(Default)]
struct ReferencedLocalsVisitor(HashSet<Local>);

impl ReferencedLocalsVisitor {
    pub fn into_hashset(self) -> HashSet<Local> {
        self.0
    }
}

impl<'tcx> Visitor<'tcx> for ReferencedLocalsVisitor {
    fn visit_rvalue(&mut self, rvalue: &Rvalue, loc: Location) {
        if let Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) = rvalue {
            if place.projection.contains(&ProjectionElem::Deref) {
                // If we're referencing a dereferenced local,
                // We don't need to put that local in memory, the referenced value is already
                // There
                return;
            }
            self.0.insert(place.local);
        }
        self.super_rvalue(rvalue, loc);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, loc: Location) {
        // Function arguments should be in memory, in case the callee references it.
        if let TerminatorKind::Call { args, .. } = &terminator.kind {
            for op in args {
                if let Operand::Copy(place) | Operand::Move(place) = op {
                    self.0.insert(place.local);
                }
            }
        }
        self.super_terminator(terminator, loc);
    }

    fn visit_place(&mut self, place: &Place<'tcx>, ctx: PlaceContext, location: Location) {
        // I don't know how to perform downcasting on values in store
        for proj in place.projection {
            if let ProjectionElem::Downcast(..) = proj {
                self.0.insert(place.local);
                break;
            }
        }
        self.super_place(place, ctx, location)
    }
}
