use super::gilsonite::{GilsoniteBuilder, ProofStep};
use super::utils::get_thir;
use super::LogicItem;
use crate::logic::gilsonite::{self, Assert};
use crate::logic::PredCtx;
use crate::prelude::*;
use crate::signature::{build_signature, make_wf_asrt, ParamKind};
use gillian::gil::{Assertion, Expr, LCmd, Lemma, SLCmd};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::GenericArgs;

use crate::temp_gen::TempGenerator;
use crate::{
    codegen::typ_encoding::TypeEncoder,
    prelude::{fatal, HasDefId, HasTyCtxt},
};

struct LemmaSig {
    name: String,
    params: Vec<String>,
}

pub(crate) struct LemmaCtx<'tcx, 'genv> {
    global_env: &'genv mut GlobalEnv<'tcx>,
    did: DefId,
    temp_gen: &'genv mut TempGenerator,
    trusted: bool,
    is_extract_lemma: bool,
}

impl<'tcx, 'genv> HasTyCtxt<'tcx> for LemmaCtx<'tcx, 'genv> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.global_env.tcx()
    }
}

impl HasDefId for LemmaCtx<'_, '_> {
    fn did(&self) -> DefId {
        self.did
    }
}

impl<'tcx> HasGlobalEnv<'tcx> for LemmaCtx<'tcx, '_> {
    fn global_env_mut(&mut self) -> &mut GlobalEnv<'tcx> {
        self.global_env
    }

    fn global_env(&self) -> &GlobalEnv<'tcx> {
        self.global_env
    }
}

impl<'tcx> TypeEncoder<'tcx> for LemmaCtx<'tcx, '_> {}

impl<'tcx, 'genv> LemmaCtx<'tcx, 'genv> {
    pub fn new(
        global_env: &'genv mut GlobalEnv<'tcx>,
        did: DefId,
        temp_gen: &'genv mut TempGenerator,
        trusted: bool,
        is_extract_lemma: bool,
    ) -> Self {
        Self {
            global_env,
            did,
            trusted,
            is_extract_lemma,
            temp_gen,
        }
    }

    fn lemma_name(&self) -> String {
        let args = GenericArgs::identity_for_item(self.tcx(), self.did());
        self.global_env.just_pred_name_with_args(self.did, args)
    }

    fn sig(&mut self) -> LemmaSig {
        let args = GenericArgs::identity_for_item(self.tcx(), self.did());
        let sig = build_signature(self.global_env, self.did(), args, &mut self.temp_gen);
        let params = sig.physical_args().map(|a| a.name().to_string()).collect();
        LemmaSig {
            name: self.lemma_name(),
            params,
        }
    }

    pub(crate) fn compile(mut self) -> Vec<LogicItem> {
        let mut res = Vec::with_capacity(1 + 3 * (self.is_extract_lemma as usize));

        let sig = self.sig();

        if self.is_extract_lemma {
            let defs = self.compile_extract_lemma(sig.name.clone(), self.did);
            res.extend(defs);
        } else if self.trusted {
            let name = sig.name.clone();

            // We set temporary hyp and conclusion, which we be replaced later by the specs
            log::debug!("Name: {}, params: {:?}", name, &sig.params);
            let mut lemma = Lemma {
                name: name.clone(),
                params: sig.params,
                hyp: Assertion::Emp,
                concs: Vec::new(),
                proof: None,
                variant: None,
                existentials: Vec::new(),
            };
            let args = GenericArgs::identity_for_item(self.tcx(), self.did());
            let sig = build_signature(self.global_env, self.did, args, &mut self.temp_gen);

            let ss = sig
                .to_gil_spec(self.global_env, name)
                .expect("Expected lemma to have contract")
                .sspecs
                .remove(0);

            lemma.hyp = ss.pre;
            lemma.concs = ss.posts;

            res.push(LogicItem::Lemma(lemma));
        } else {
            let (thir, expr) = get_thir!(self, self.did);
            let ctx = GilsoniteBuilder::new(thir.clone(), self.tcx());

            let proof = ctx.build_lemma_proof(expr);

            res.push(self.compile_proof(proof));
            // fatal!(self, "Can't compile untrusted lemmas yet")
        }
        res
    }

    fn compile_proof(&mut self, proof: Vec<ProofStep<'tcx>>) -> LogicItem {
        let args = GenericArgs::identity_for_item(self.tcx(), self.did());

        let mut temp_gen = TempGenerator::new();

        let name = self.global_env.just_pred_name(self.did);

        let mut pred_ctx =
            PredCtx::new_with_identity_args(self.global_env, &mut temp_gen, self.did);

        let gil_proof = Self::compile_proof_steps(&mut pred_ctx, proof);
        let mut sig = build_signature(self.global_env, self.did, args, &mut temp_gen);

        let params = sig.physical_args().map(|a| a.name().to_string()).collect();

        let proof_lemma = Lemma {
            name,
            params,
            hyp: sig.user_pre().unwrap().clone(),
            concs: vec![sig.user_post().unwrap().clone()],
            proof: Some(gil_proof),
            variant: None,
            existentials: vec![],
        };

        LogicItem::Lemma(proof_lemma)
    }

    fn compile_proof_steps(
        pred_ctx: &mut PredCtx<'tcx, '_>,
        proof: Vec<ProofStep<'tcx>>,
    ) -> Vec<LCmd> {
        let mut gil_proof = Vec::new();
        for s in proof {
            match s {
                ProofStep::Package { pre, post } => {
                    gil_proof.push(LCmd::SL(SLCmd::Package {
                        lhs: pred_ctx.compile_pred_call(pre),

                        rhs: pred_ctx.compile_pred_call(post),
                    }));
                }
                ProofStep::Unfold { pred } => {
                    let (pred_name, parameters) = pred_ctx.compile_pred_call(pred);
                    gil_proof.push(LCmd::SL(SLCmd::Unfold {
                        pred_name,
                        parameters,
                        bindings: None,
                        rec: false,
                    }))
                }
                ProofStep::Fold { pred } => {
                    let (pred_name, parameters) = pred_ctx.compile_pred_call(pred);
                    gil_proof.push(LCmd::SL(SLCmd::Fold {
                        pred_name,
                        parameters,
                        bindings: None,
                    }))
                }
                ProofStep::If {
                    cond,
                    t_branch,
                    f_branch,
                } => {
                    let guard = pred_ctx.compile_expression(cond);
                    let then_branch = Self::compile_proof_steps(pred_ctx, t_branch);
                    let else_branch = Self::compile_proof_steps(pred_ctx, f_branch);
                    gil_proof.push(LCmd::If {
                        guard,
                        then_branch,
                        else_branch,
                    });
                }
                ProofStep::Auto => {}
                ProofStep::Call { pred } => {
                    let (lemma_name, parameters) = pred_ctx.compile_pred_call(pred);
                    gil_proof.push(LCmd::SL(SLCmd::ApplyLem {
                        lemma_name,
                        parameters,
                        existentials: Vec::new(),
                    }))
                } // _ => todo!(),
            };
        }
        gil_proof
    }

    fn compile_extract_lemma(&mut self, _: String, id: DefId) -> Vec<LogicItem> {
        let name = self.global_env.extract_lemma_name(id);
        let name = name.clone() + "$$extract_proof";
        let post_name = name.clone() + "$$post";
        let pre_name = name.clone() + "$$pre";
        let args = GenericArgs::identity_for_item(self.tcx(), self.did());

        let extract_term = {
            let (thir, e) = get_thir!(self.global_env, self.did);
            let g = GilsoniteBuilder::new(thir.clone(), self.tcx());
            g.build_extract_lemma(e)
        };

        let mut temp_gen = TempGenerator::new();

        {
            // HACK to compile the preds. should do this cleanly
            let mut pred_ctx =
                PredCtx::new_with_identity_args(self.global_env, &mut temp_gen, self.did);

            let _ = pred_ctx.compile_assertion(Assert {
                kind: gilsonite::AssertKind::Call(extract_term.from.clone()),
            });
            let _ = pred_ctx.compile_assertion(Assert {
                kind: gilsonite::AssertKind::Call(extract_term.extract.clone()),
            });
        };

        let mut sig = build_signature(self.global_env, self.did(), args, &mut temp_gen);

        let mut temp_gen = TempGenerator::new();
        let param_env = self.tcx().param_env(self.did);

        let pre_inner = self
            .global_env
            .resolve_inner_pred(extract_term.from.def_id, extract_term.from.substs);

        // TODO: move into resolve_inner_pred
        let post = self
            .global_env
            .try_resolve(
                param_env,
                extract_term.extract.def_id,
                extract_term.extract.substs,
            )
            .unwrap_or((extract_term.extract.def_id, extract_term.extract.substs));

        let post_inner = self.global_env.resolve_inner_pred(post.0, post.1);

        let ty_wf = sig.type_wf_pres(self.global_env);

        let models_wf: Vec<Assertion> = extract_term
            .uni
            .iter()
            .map(|a| {
                Expr::PVar(a.0.to_string())
                    .eq_f(Expr::LVar(format!("#{}", a.0)))
                    .into()
            })
            .chain(extract_term.uni.iter().map(|a| {
                make_wf_asrt(
                    self.global_env,
                    sig.temp_gen,
                    Expr::LVar(format!("#{}", a.0)),
                    a.1,
                )
            }))
            .collect();

        let mut pred_ctx =
            PredCtx::new_with_identity_args(self.global_env, &mut temp_gen, self.did);

        let mut res = Vec::new();

        let non_lvars: Vec<_> = sig
            .args
            .iter()
            .skip(1)
            .filter(|p| !matches!(p, ParamKind::Logic(_, _)))
            .collect();
        let ins: Vec<_> = (0..non_lvars.len()).collect();

        let uni_vars = extract_term
            .uni
            .into_iter()
            .map(|(s, _)| (s.to_string(), None));

        let params: Vec<_> = non_lvars
            .into_iter()
            .map(|p| (p.name().to_string(), None))
            .chain(uni_vars)
            .collect();

        let assuming = pred_ctx.compile_formula(extract_term.assuming);

        let (from_args, remainder) = {
            let post = pred_ctx.compile_assertion(Assert {
                kind: gilsonite::AssertKind::Call(extract_term.from),
            });

            let mut splat = post.unstar();

            let Assertion::Pred { params, .. } = splat.remove(0) else {
                fatal!(
                    self,
                    "unreachable: expected `extract` to be a predicate call"
                )
            };
            // TODO assert first argument is a lifetime
            let mut params = params.clone();
            params.remove(0);

            (params, splat)
        };

        let from = Assertion::pred_call_of_tuple((pre_inner, from_args));

        let def = sig
            .store_eq_var()
            .into_iter()
            .chain(models_wf.clone())
            .chain(ty_wf.clone())
            .chain([assuming.into()])
            .chain(remainder)
            .fold(from, Assertion::star);

        // let def: Assertion = from.star(assuming.into());
        // What we will extract from
        let wand_pre = Pred {
            name: pre_name.clone(),
            num_params: 0,
            params: params.clone(),
            ins,
            definitions: vec![def],
            pure: false,
            abstract_: false,
            facts: vec![],
            guard: None,
        };

        res.push(LogicItem::Pred(wand_pre));

        let (extract_args, remainder) = {
            let post = pred_ctx.compile_assertion(Assert {
                kind: gilsonite::AssertKind::Call(extract_term.extract),
            });

            let mut splat = post.unstar();

            let Assertion::Pred { params, .. } = splat.remove(0) else {
                fatal!(
                    self,
                    "unreachable: expected `extract` to be a predicate call"
                )
            };
            // TODO assert first argument is a lifetime
            let mut params = params.clone();
            params.remove(0);

            (params, splat)
        };

        let extract = sig
            .store_eq_var()
            .into_iter()
            .chain(ty_wf)
            .chain(models_wf.clone())
            .chain(remainder)
            .fold(
                Assertion::pred_call_of_tuple((post_inner, extract_args)),
                Assertion::star,
            );

        let ins = (0..params.len()).collect();
        // What we extract from the body
        let wand_post = Pred {
            name: post_name.clone(),
            num_params: 0,
            params: params.clone(),
            ins,
            definitions: vec![extract],
            pure: false,
            abstract_: false,
            facts: vec![],
            guard: None,
        };

        res.push(LogicItem::Pred(wand_post));

        let params: Vec<_> = params.into_iter().map(|a| a.0).collect();
        let args: Vec<_> = params.iter().map(|e| Expr::LVar(format!("#{e}"))).collect();

        let pre_call_tup = (pre_name.clone(), args.clone());
        let post_call_tup = (post_name.clone(), args.clone());

        let proof = {
            vec![LCmd::SL(SLCmd::Package {
                lhs: post_call_tup.clone(),
                rhs: pre_call_tup.clone(),
            })]
        };

        let conc = Assertion::pred_call_of_tuple(post_call_tup.clone())
            .clone()
            .star(Assertion::wand(post_call_tup, pre_call_tup.clone()));

        let proof_lemma = Lemma {
            name,
            params,
            hyp: Assertion::pred_call_of_tuple(pre_call_tup),
            concs: vec![conc],
            proof: Some(proof),
            variant: None,
            existentials: vec![],
        };

        res.push(LogicItem::Lemma(proof_lemma));

        res
    }
}
