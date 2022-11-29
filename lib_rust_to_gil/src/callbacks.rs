use std::collections::HashMap;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::WithOptConstParam;

use super::config::Config;
use crate::logic::{compile_logic, LogicItem};
use crate::prelude::*;
use crate::utils::cleanup_logic::cleanup_logic;

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
        let mut pre_tbl = HashMap::new();
        let mut post_tbl = HashMap::new();
        let mut spec_tbl = HashMap::new();
        for key in tcx.hir().body_owners() {
            let did = key.to_def_id();
            if crate::utils::attrs::is_logic(did, *tcx) {
                let logic_item = compile_logic(did, *tcx, &mut global_env);
                match logic_item {
                    LogicItem::Pred(pred) => prog.add_pred(pred),
                    LogicItem::Precondition(symbol, asrt) => {
                        pre_tbl.insert(symbol, asrt);
                    }
                    LogicItem::Postcondition(symbol, asrt) => {
                        post_tbl.insert(symbol, asrt);
                    }
                }
            } else {
                if let Some(pre_id) = crate::utils::attrs::get_pre_id(did, *tcx) {
                    let proc_name =
                        rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(did));
                    let post_id =
                        crate::utils::attrs::get_post_id(did, *tcx).unwrap_or_else(|| {
                            tcx.sess.fatal(format!(
                                "Precondition without postcondition for {}",
                                tcx.def_path_str(did)
                            ))
                        });
                    spec_tbl.insert(proc_name, (pre_id, post_id));
                }
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
        }
        global_env.add_all_procs(&mut prog);
        for (key, (pre_id, post_id)) in spec_tbl {
            dbg!("adding spec for {}", &key);
            let pre = pre_tbl.remove(&pre_id).unwrap_or_else(|| {
                tcx.sess
                    .fatal(format!("Precondition {} not found for {}", pre_id, key))
            });
            let post = post_tbl.remove(&post_id).unwrap_or_else(|| {
                tcx.sess
                    .fatal(format!("Postcondition {} not found for {}", post_id, key))
            });
            let sspec = gillian::gil::SingleSpec {
                pre,
                posts: vec![post],
                flag: gillian::gil::Flag::Normal,
                to_verify: true,
            };
            prog.add_sspec_to_existing_proc(key, sspec);
        }
        let init_data = global_env.serialized_adt_declarations();
        ParsingUnit { prog, init_data }
    }
}

impl Callbacks for ToGil {
    fn config(&mut self, config: &mut rustc_interface::Config) {
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
            let prog = self.compile_prog(&tcx);
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
