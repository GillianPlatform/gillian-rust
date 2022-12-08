use std::collections::HashMap;

use rustc_hir::def::DefKind;
use rustc_middle::ty::WithOptConstParam;

use crate::config::Config;
use crate::logic::{compile_logic, LogicItem};
use crate::prelude::*;

pub struct ProgCtx<'tcx, 'comp> {
    tcx: TyCtxt<'tcx>,
    config: &'comp Config,
    prog: gillian::gil::Prog,
    global_env: GlobalEnv<'tcx>,
    pre_tbl: HashMap<Symbol, (Vec<String>, Assertion)>,
    post_tbl: HashMap<Symbol, Assertion>,
    spec_tbl: HashMap<String, (Symbol, Symbol)>,
}

impl CanFatal for ProgCtx<'_, '_> {
    fn fatal(&self, str: &str) -> ! {
        self.tcx.sess.fatal(str)
    }
}

impl<'tcx, 'comp> ProgCtx<'tcx, 'comp> {
    fn new(tcx: TyCtxt<'tcx>, config: &'comp Config) -> Self {
        Self {
            prog: gillian::gil::Prog::new(runtime::imports()),
            global_env: GlobalEnv::new(tcx),
            pre_tbl: HashMap::new(),
            post_tbl: HashMap::new(),
            spec_tbl: HashMap::new(),
            tcx,
            config,
        }
    }

    fn compile_logic(&mut self, did: DefId) {
        let logic_item = compile_logic(did, self.tcx, &mut self.global_env);
        match logic_item {
            LogicItem::Pred(pred) => self.prog.add_pred(pred),
            LogicItem::Precondition(symbol, args, asrt) => {
                self.pre_tbl.insert(symbol, (args, asrt));
            }
            LogicItem::Postcondition(symbol, asrt) => {
                self.post_tbl.insert(symbol, asrt);
            }
        }
    }

    fn compile_fn(&mut self, did: DefId) {
        if let Some(pre_id) = crate::utils::attrs::get_pre_id(did, self.tcx) {
            let proc_name =
                rustc_middle::ty::print::with_no_trimmed_paths!(self.tcx.def_path_str(did));
            let post_id = crate::utils::attrs::get_post_id(did, self.tcx).unwrap_or_else(|| {
                self.tcx.sess.fatal(format!(
                    "Precondition without postcondition for {}",
                    proc_name
                ))
            });
            self.spec_tbl.insert(proc_name, (pre_id, post_id));
        }
        let body = match self.tcx.def_kind(did) {
            DefKind::Ctor(..) => self.tcx.optimized_mir(did),
            _ => std::cell::Ref::leak(
                self.tcx
                    .mir_promoted(WithOptConstParam::unknown(did.expect_local()))
                    .0
                    .borrow(),
            ),
        };
        let ctx = GilCtxt::new(did, self.config, body, self.tcx, &mut self.global_env);
        self.prog.add_proc(ctx.push_body());
    }

    /// Careful, after calling add_specs, the spec table is emptied
    fn add_specs(&mut self) {
        let spec_tbl = std::mem::take(&mut self.spec_tbl);
        for (key, (pre_id, post_id)) in spec_tbl {
            log::debug!("adding spec for {}", &key);
            let (pre_args, mut pre) = self
                .pre_tbl
                .remove(&pre_id)
                .unwrap_or_else(|| fatal!(self, "Precondition {} not found for {}", pre_id, key));
            let mut post = self
                .post_tbl
                .remove(&post_id)
                .unwrap_or_else(|| fatal!(self, "Postcondition {} not found for {}", post_id, key));
            let proc_args = self
                .prog
                .procs
                .get(&key)
                .expect("proc not found")
                .params
                .clone();
            if pre_args.len() != proc_args.len() {
                fatal!(
                    self,
                    "MIR fonction has more arguments that its THIR, can't handle that?"
                )
            }
            let mapping: HashMap<_, _> = pre_args.into_iter().zip(proc_args).collect();
            pre.subst_pvar(&mapping);
            post.subst_pvar(&mapping);
            let sspec = gillian::gil::SingleSpec {
                pre,
                posts: vec![post],
                flag: gillian::gil::Flag::Normal,
                to_verify: true,
            };
            let proc = self.prog.procs.get_mut(&key).unwrap();
            match &mut proc.spec {
                Some(spec) => spec.sspecs.push(sspec),
                None => {
                    proc.spec = Some(Spec {
                        name: proc.name.clone(),
                        params: proc.params.clone(),
                        sspecs: vec![sspec],
                        to_verify: true,
                    })
                }
            }
        }
    }

    fn final_prog(mut self) -> ParsingUnit {
        for key in self.tcx.hir().body_owners() {
            let did = key.to_def_id();
            if crate::utils::attrs::is_logic(did, self.tcx) {
                self.compile_logic(did);
            } else {
                self.compile_fn(did);
            }
        }
        self.global_env.add_all_procs(&mut self.prog);
        self.add_specs();
        let init_data = self.global_env.serialized_adt_declarations();
        ParsingUnit {
            prog: self.prog,
            init_data,
        }
    }

    pub(crate) fn compile_prog(tcx: TyCtxt<'tcx>, config: &'comp Config) -> ParsingUnit {
        let this = Self::new(tcx, config);
        this.final_prog()
    }
}
