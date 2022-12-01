use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};

use super::config::Config;
use crate::utils::cleanup_logic::cleanup_logic;

#[derive(Debug)]
pub struct ToGil {
    opts: Config,
}

impl ToGil {
    pub fn new(opts: Config) -> Self {
        Self { opts }
    }
}

impl Callbacks for ToGil {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        let _ = self.opts;
        config.override_queries = Some(|_sess, providers, _external_providers| {
            providers.mir_built = |tcx, def_id| {
                let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
                let mut mir = mir.steal();
                cleanup_logic(tcx, def_id.def_id_for_type_of(), &mut mir);
                tcx.alloc_steal_mir(mir)
            }
        })
    }

    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        queries.prepare_outputs().unwrap();
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            let prog = super::prog_context::ProgCtx::compile_prog(tcx);
            let tmp_file = tcx.output_filenames(()).temp_path_ext("gil", None);
            log::debug!("Writing to {:#?}", &tmp_file);
            if let Err(err) = std::fs::write(&tmp_file, prog.to_string()) {
                tcx.sess
                    .fatal(format!("Error writing in GIL file: {}", err))
            }
        });

        compiler.session().abort_if_errors();

        Compilation::Stop
    }
}
