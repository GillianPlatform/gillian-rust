use std::collections::HashMap;

use rustc_hir::def::DefKind;
use rustc_middle::ty::WithOptConstParam;

use super::temp_gen::TempGenerator;
use crate::config::Config;
use crate::logic::{compile_logic, LogicItem};
use crate::prelude::*;

pub struct ProgCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    prog: gillian::gil::Prog,
    global_env: GlobalEnv<'tcx>,
    pre_tbl: HashMap<Symbol, (Vec<String>, Assertion)>,
    post_tbl: HashMap<Symbol, Assertion>,
    spec_tbl: HashMap<String, (Symbol, Symbol)>,
    temp_gen: TempGenerator,
}

impl<'tcx> HasTyCtxt<'tcx> for ProgCtx<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx, 'comp> ProgCtx<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, config: Config) -> Self {
        Self {
            prog: gillian::gil::Prog::new(runtime::imports(config.prophecies)),
            global_env: GlobalEnv::new(tcx, config),
            temp_gen: TempGenerator::new(),
            pre_tbl: HashMap::new(),
            post_tbl: HashMap::new(),
            spec_tbl: HashMap::new(),
            tcx,
        }
    }

    fn compile_logic(&mut self, did: DefId) {
        let logic_item = compile_logic(did, self.tcx(), &mut self.global_env, &mut self.temp_gen);
        if let Some(logic_item) = logic_item {
            match logic_item {
                LogicItem::Pred(pred) => self.prog.add_pred(pred),
                LogicItem::Lemma(lemma) => {
                    let pre_id = crate::utils::attrs::get_pre_id(did, self.tcx());
                    let post_id = crate::utils::attrs::get_post_id(did, self.tcx());
                    let name = rustc_middle::ty::print::with_no_trimmed_paths!(self
                        .tcx()
                        .def_path_str(did));
                    match (pre_id, post_id) {
                        (Some(pre_id), Some(post_id)) => {
                            self.spec_tbl.insert(name, (pre_id, post_id));
                        }
                        (Some(_), None) | (None, Some(_)) => {
                            fatal!(
                                self,
                                "Missing precondition or postcondition for lemma: {:?}",
                                did
                            )
                        }
                        (None, None) => (),
                    }
                    self.prog.add_lemma(lemma)
                }
                LogicItem::Precondition(symbol, args, asrt) => {
                    self.pre_tbl.insert(symbol, (args, asrt));
                }
                LogicItem::Postcondition(symbol, asrt) => {
                    self.post_tbl.insert(symbol, asrt);
                }
            }
        }
    }

    fn compile_fn(&mut self, did: DefId) {
        let pre_id = crate::utils::attrs::get_pre_id(did, self.tcx());
        let post_id = crate::utils::attrs::get_post_id(did, self.tcx());
        let proc_name =
            rustc_middle::ty::print::with_no_trimmed_paths!(self.tcx().def_path_str(did));
        let body = match self.tcx().def_kind(did) {
            DefKind::Ctor(..) => self.tcx().optimized_mir(did),
            _ => std::cell::Ref::leak(
                self.tcx()
                    .mir_promoted(WithOptConstParam::unknown(did.expect_local()))
                    .0
                    .borrow(),
            ),
        };
        let ctx = GilCtxt::new(self.tcx(), body, &mut self.global_env);
        match (pre_id, post_id) {
            (Some(pre_id), Some(post_id)) => {
                self.spec_tbl.insert(proc_name, (pre_id, post_id));
            }
            (None, Some(post_id)) => {
                let pre_id = Symbol::intern(&format!("{}_pre____", proc_name));
                let assertion = crate::logic::dummy_pre(self.tcx, did);
                self.pre_tbl.insert(pre_id, (ctx.args(), assertion));
                self.spec_tbl.insert(proc_name, (pre_id, post_id));
            }
            (Some(_), None) => fatal!(
                self,
                "Pre-condition without post-condition for {}",
                proc_name
            ),
            (None, None) => (),
        }
        self.prog.add_proc(ctx.push_body());
    }

    fn add_spec_to_proc(&mut self, key: String, pre_id: Symbol, post_id: Symbol) {
        let proc_args = self
            .prog
            .procs
            .get(&key)
            .expect("proc not found")
            .params
            .clone()
            .into_iter()
            .map(Expr::PVar);
        let pre = {
            let (pre_args, mut pre) = self
                .pre_tbl
                .remove(&pre_id)
                .unwrap_or_else(|| fatal!(self, "Precondition {} not found for {}", pre_id, key));
            if pre_args.len() != proc_args.len() {
                fatal!(
                    self,
                    "MIR ({:?}) function has more arguments than its THIR, can't handle that?\nPRE: {:?}\nFN:  {:?}", key,
                    pre_args, proc_args
                )
            }
            let mapping: HashMap<_, _> = pre_args.into_iter().zip(proc_args).collect();
            pre.subst_pvar(&mapping);
            pre
        };
        let post = self
            .post_tbl
            .remove(&post_id)
            .unwrap_or_else(|| fatal!(self, "Postcondition {} not found for {}", post_id, key));

        let sspec = gillian::gil::SingleSpec {
            pre,
            posts: vec![post],
            flag: gillian::gil::Flag::Normal,
        };
        let proc = self.prog.procs.get_mut(&key).unwrap();
        match &mut proc.spec {
            Some(spec) => spec.sspecs.push(sspec),
            None => {
                proc.spec = Some(Spec {
                    name: proc.name.clone(),
                    params: proc.params.clone(),
                    sspecs: vec![sspec],
                })
            }
        }
    }

    fn add_spec_to_lemma(&mut self, key: String, pre_id: Symbol, post_id: Symbol) {
        // While for procs we need safe-guards in case MIR has changed things compared to THIR,
        // Lemmas come from THIR and therefore should be safe to handle.
        let pre = self
            .pre_tbl
            .remove(&pre_id)
            .unwrap_or_else(|| fatal!(self, "Precondition {} not found for {}", pre_id, key))
            .1;
        let post = self
            .post_tbl
            .remove(&post_id)
            .unwrap_or_else(|| fatal!(self, "Postcondition {} not found for {}", post_id, key));

        let lemma = self.prog.lemmas.get_mut(&key).unwrap();
        lemma.hyp = pre;
        lemma.concs = vec![post];
    }

    // Careful, after calling add_specs, the spec table is emptied
    fn add_specs(&mut self) {
        let spec_tbl = std::mem::take(&mut self.spec_tbl);
        for (key, (pre_id, post_id)) in spec_tbl {
            log::debug!("adding spec for {}", &key);
            if self.prog.procs.contains_key(&key) {
                self.add_spec_to_proc(key, pre_id, post_id)
            } else {
                self.add_spec_to_lemma(key, pre_id, post_id)
            }
        }
    }

    fn final_prog(mut self) -> ParsingUnit {
        for key in self.tcx().hir().body_owners() {
            let did = key.to_def_id();
            if crate::utils::attrs::is_logic(did, self.tcx()) {
                self.compile_logic(did);
            } else {
                self.compile_fn(did);
            }
        }
        self.add_specs();
        self.global_env.flush_remaining_defs_to_prog(&mut self.prog);
        let init_data = self.global_env.serialized_adt_declarations();
        ParsingUnit {
            prog: self.prog,
            init_data,
        }
    }

    pub(crate) fn compile_prog(tcx: TyCtxt<'tcx>, config: Config) -> ParsingUnit {
        let this = Self::new(tcx, config);
        this.final_prog()
    }
}
