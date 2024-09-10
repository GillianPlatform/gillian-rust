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
        let sig = build_signature(self.global_env, self.did(), args, self.temp_gen);
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
            // let defs = self.compile_extract_lemma(sig.name.clone(), self.did);
            // res.extend(defs);
        } else if self.trusted {
            let name = sig.name.clone();

            // We set temporary hyp and conclusion, which we be replaced later by the specs
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
            let sig = build_signature(self.global_env, self.did, args, self.temp_gen);

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

        let params = sig.all_vars().map(|a| a.0.to_string()).collect();

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
                ProofStep::Call { pred } => {
                    let (lemma_name, parameters) = pred_ctx.compile_pred_call(pred);
                    gil_proof.push(LCmd::SL(SLCmd::ApplyLem {
                        lemma_name,
                        parameters,
                        existentials: Vec::new(),
                    }))
                }
                ProofStep::AssertBind { assertion, vars } => {
                    let assertion = pred_ctx.compile_assertion(assertion);

                    gil_proof.push(LCmd::SL(SLCmd::SepAssert {
                        assertion,
                        existentials: vars.iter().map(|v| format!("#{v}")).collect(),
                    }))
                }
            };
        }
        gil_proof
    }

    fn compile_extract_lemma(&mut self, _: String, id: DefId) -> Vec<LogicItem> {
       unreachable!()
    }
}
