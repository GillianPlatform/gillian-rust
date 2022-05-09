use rustc_span::def_id::DefId;

use super::names::{gil_temp_from_id, temp_name_from_local};
use crate::prelude::*;

pub struct GilCtxt<'tcx, 'body> {
    did: DefId,
    pub(crate) ty_ctxt: TyCtxt<'tcx>,
    gil_body: ProcBody,
    gil_temp_counter: usize,
    switch_label_counter: usize,
    next_label: Option<String>,
    mir: &'body Body<'tcx>,
    pub(crate) global_env: &'body mut GlobalEnv<'tcx>,
}

impl<'tcx, 'body> CanFatal for GilCtxt<'tcx, 'body> {
    fn fatal(&self, str: &str) -> ! {
        self.ty_ctxt.sess.fatal(str)
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
            ty_ctxt,
            gil_temp_counter: 0,
            switch_label_counter: 0,
            gil_body: ProcBody::default(),
            next_label: None,
            mir,
            global_env,
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
