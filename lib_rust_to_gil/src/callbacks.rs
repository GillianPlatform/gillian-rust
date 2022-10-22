use super::config::Config;
use crate::prelude::*;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::WithOptConstParam;

#[derive(Debug)]
pub struct ToGil {
    opts: Config,
}

impl ToGil {
    pub fn new(opts: Config) -> Self {
        Self { opts }
    }

    fn compile_prog<'gil>(&self, tcx: &'gil TyCtxt) -> gillian::gil::ParsingUnit {
        let _ = self.opts;
        let mut prog = gillian::gil::Prog::new(runtime::imports());
        let mut global_env = GlobalEnv::new(*tcx);
        for key in tcx.mir_keys(()) {
            let did = key.to_def_id();
            let body = match tcx.def_kind(did) {
                DefKind::Ctor(..) => tcx.optimized_mir(did),
                _ => std::cell::Ref::leak(
                    tcx.mir_promoted(WithOptConstParam::unknown(did.expect_local()))
                        .0
                        .borrow(),
                ),
            };
            let ctx = GilCtxt::new(did, body, *tcx, &mut global_env);
            prog.add_proc(ctx.push_body());
        }
        global_env.add_all_procs(&mut prog);
        let init_data = global_env.serialized_adt_declarations();
        ParsingUnit { prog, init_data }
    }
}

impl Callbacks for ToGil {
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        queries.prepare_outputs().unwrap();
        queries.global_ctxt().unwrap();
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let prog = self.compile_prog(&tcx);
            let tmp_file = tcx.output_filenames(()).temp_path_ext("gil", None);
            log::debug!("Writing to {:#?}", &tmp_file);
            if let Err(err) = std::fs::write(&tmp_file, prog.to_string()) {
                tcx.sess
                    .fatal(&format!("Error writing in GIL file: {}", err))
            }
        });

        compiler.session().abort_if_errors();

        Compilation::Stop
    }
}
