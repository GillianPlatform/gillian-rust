use std::{cell::RefCell, collections::HashMap, io::stdout};

use rustc_borrowck::consumers::{BodyWithBorrowckFacts, ConsumerOptions};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;

use super::config::Config;
use crate::{global_env::GlobalEnv, metadata, utils::cleanup_logic::cleanup_logic};

#[derive(Debug)]
pub struct ToGil {
    opts: Config,
}

impl ToGil {
    pub fn new(opts: Config) -> Self {
        Self { opts }
    }
}

thread_local! {
    pub static MIR_BODIES:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::new());
}

impl Callbacks for ToGil {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        let _ = self.opts;
        config.override_queries = Some(|_sess, providers| {
            providers.mir_built = |tcx, def_id: rustc_span::def_id::LocalDefId| {
                let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
                let mut mir = mir.steal();
                cleanup_logic(tcx, def_id.to_def_id(), &mut mir);
                tcx.alloc_steal_mir(mir)
            };

            // providers.mir_drops_elaborated_and_const_checked = |tcx, def_id| {
            //     let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS
            //         .mir_drops_elaborated_and_const_checked)(tcx, def_id);
            //     let mut mir = mir.steal();
            //     remove_ghost_closures(tcx, &mut mir);
            //     tcx.alloc_steal_mir(mir)
            // };

            providers.mir_borrowck = |tcx, def_id| {
                let opts = ConsumerOptions::PoloniusInputFacts;

                let body_with_facts =
                    rustc_borrowck::consumers::get_body_with_borrowck_facts(tcx, def_id, opts);

                // SAFETY: The reader casts the 'static lifetime to 'tcx before using it.
                let body_with_facts: BodyWithBorrowckFacts<'static> =
                    unsafe { std::mem::transmute(body_with_facts) };

                MIR_BODIES.with(|state| {
                    let mut map = state.borrow_mut();
                    assert!(map.insert(def_id, body_with_facts).is_none());
                });

                (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_borrowck)(tcx, def_id)
            }
        })
    }

    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            let mut global_env = GlobalEnv::new(tcx, self.opts.clone());
            let (prog, metadata) =
                super::prog_context::ProgCtx::compile_prog(tcx, &mut global_env, self.opts.clone());
            let tmp_file = tcx.output_filenames(()).temp_path_ext("gil", None);

            if self.opts.in_test {
                let mut out = stdout().lock();
                use std::io::Write;
                write!(out, "{prog}").unwrap();
            } else {
                log::trace!("Writing to {:#?}", &tmp_file);

                if let Err(err) = std::fs::write(&tmp_file, prog.to_string()) {
                    tcx.dcx()
                        .fatal(format!("Error writing in GIL file: {}", err))
                }
            }

            metadata::dump_exports(tcx, metadata, &None);
        });

        compiler.sess.dcx().abort_if_errors();

        Compilation::Continue
    }
}

/// Trys to retrieve the promoted MIR for a body from a thread local cache.
/// The cache is populated when rustc runs the `mir_borrowck` query.
/// After a body was retrieved, calling this function again for the same `def_id` will return `None`.
pub fn get_body(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Option<BodyWithBorrowckFacts<'_>> {
    // trigger borrow checking
    let _ = tcx.mir_borrowck(def_id);

    MIR_BODIES.with(|state| {
        let mut map = state.borrow_mut();
        // SAFETY: For soundness we need to ensure that the bodies have
        // the same lifetime (`'tcx`), which they had before they were
        // stored in the thread local.
        map.remove(&def_id)
            .map(|body| unsafe { std::mem::transmute(body) })
    })
}
