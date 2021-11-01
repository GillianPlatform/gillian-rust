use super::names::{gil_temp_from_id, ret_var, temp_name_from_local};
use crate::prelude::*;

pub struct GilCtxt<'tcx> {
    pub(crate) instance: Instance<'tcx>,
    pub(crate) ty_ctxt: TyCtxt<'tcx>,
    gil_body: ProcBody,
    gil_temp_counter: u32,
    next_label: Option<String>,
}

impl<'tcx> GilCtxt<'tcx> {
    pub fn new(instance: Instance<'tcx>, ty_ctxt: TyCtxt<'tcx>) -> Self {
        GilCtxt {
            instance,
            ty_ctxt,
            gil_temp_counter: 0,
            gil_body: ProcBody::default(),
            next_label: None,
        }
    }

    pub fn mir(&self) -> &'tcx Body<'tcx> {
        self.ty_ctxt.instance_mir(self.instance.def)
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

    pub fn sanitized_original_name_from_local(&self, local: &Local) -> Option<String> {
        self.original_name_from_local(local)
            .map(names::sanitize_name)
    }

    pub fn name_from_local(&self, local: &Local) -> String {
        if *local == RETURN_PLACE {
            ret_var()
        } else {
            match self.sanitized_original_name_from_local(local) {
                Some(name) => name,
                None => temp_name_from_local(local),
            }
        }
    }

    pub fn temp_var(&mut self) -> String {
        let current = self.gil_temp_counter;
        self.gil_temp_counter += 1;
        gil_temp_from_id(current)
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
