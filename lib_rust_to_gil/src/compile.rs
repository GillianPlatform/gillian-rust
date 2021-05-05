// use rustc_middle::mir::*;
use rustc_hir::def_id::{LocalDefId, LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;
// use rustc_middle::mir::{Body};
use super::gil;

pub struct ToGilTyCtxt<'tcx>(TyCtxt<'tcx>);

impl<'tcx> ToGilTyCtxt<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        ToGilTyCtxt(tcx)
    }

    fn compile_body(&self, key: &LocalDefId) -> gil::Proc {
        let proc_name = self.0.item_name(key.to_def_id());
        gil::Proc::new(proc_name.to_string())
    }

    pub fn compile_prog(&self) -> gil::Prog {
        let procs: Vec<gil::Proc> = self
            .0
            .mir_keys(LOCAL_CRATE)
            .iter()
            .map(|key| self.compile_body(key))
            .collect();
        log::debug!("{:#?}", procs);
        // let mir_main = self.0.optimized_mir(*key);
        // log::debug!("{:#?}", mir_main);
        // let gil_main = self.compile_function(mir_main);
        // log::debug!("{:#?}", gil_main);
        gil::Prog::default()
    }
}
