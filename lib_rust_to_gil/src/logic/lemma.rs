use super::gilsonite::{GilsoniteBuilder, ProofStep};
use super::predicate::CallerKind;
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
    ) -> Self {
        Self {
            global_env,
            did,
            trusted,

            temp_gen,
        }
    }

    fn lemma_name(&self) -> String {
        let args = GenericArgs::identity_for_item(self.tcx(), self.did());
        self.global_env.just_def_name_with_args(self.did, args)
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

    pub(crate) fn compile(mut self) -> Lemma {
        let name = self.lemma_name();
        self.global_env_mut().mark_as_compiled(name.clone());
        if self.trusted {
            let sig = self.sig();

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
                .into_gil_spec(self.global_env, name)
                .expect("Expected lemma to have contract")
                .sspecs
                .remove(0);

            lemma.hyp = ss.pre;
            lemma.concs = ss.posts;

            lemma
        } else {
            let (thir, expr) = get_thir!(self, self.did);
            let ctx = GilsoniteBuilder::new(thir.clone(), self.tcx());

            let proof = ctx.build_lemma_proof(expr);

            self.compile_proof(proof)
        }
    }

    fn compile_proof(&mut self, proof: Vec<ProofStep<'tcx>>) -> Lemma {
        let args = GenericArgs::identity_for_item(self.tcx(), self.did());

        let mut temp_gen = TempGenerator::new();

        let name = self.global_env.just_def_name(self.did);

        let mut pred_ctx =
            PredCtx::new_with_identity_args(self.global_env, &mut temp_gen, self.did);

        let gil_proof = Self::compile_proof_steps(&mut pred_ctx, proof);
        let mut sig = build_signature(self.global_env, self.did, args, &mut temp_gen);

        let params: Vec<_> = sig.physical_args().map(|a| a.name().to_string()).collect();

        let proof_lemma = Lemma {
            name,
            params,
            hyp: sig.user_pre().unwrap().clone().pvar_to_lvar(),
            concs: vec![sig.user_post().unwrap().clone().pvar_to_lvar()],
            proof: Some(gil_proof),
            variant: None,
            existentials: vec![],
        };

        proof_lemma
    }

    fn compile_proof_steps(
        pred_ctx: &mut PredCtx<'tcx, '_>,
        proof: Vec<ProofStep<'tcx>>,
    ) -> Vec<LCmd> {
        let mut gil_proof = Vec::new();
        for s in proof {
            match s {
                ProofStep::Package { pre, post } => {
                    let mut lhs = pred_ctx.compile_call(pre, CallerKind::Pred);
                    let mut rhs = pred_ctx.compile_call(post, CallerKind::Pred);
                    lhs.1 = lhs.1.into_iter().map(Expr::pvar_to_lvar).collect();
                    rhs.1 = rhs.1.into_iter().map(Expr::pvar_to_lvar).collect();

                    gil_proof.push(LCmd::SL(SLCmd::Package { lhs, rhs }));
                }
                ProofStep::Unfold { pred } => {
                    let (pred_name, parameters) = pred_ctx.compile_call(pred, CallerKind::Pred);
                    gil_proof.push(LCmd::SL(SLCmd::Unfold {
                        pred_name,
                        parameters: parameters.into_iter().map(|p| p.pvar_to_lvar()).collect(),
                        bindings: None,
                        rec: false,
                    }))
                }
                ProofStep::Fold { pred } => {
                    let (pred_name, parameters) = pred_ctx.compile_call(pred, CallerKind::Pred);
                    gil_proof.push(LCmd::SL(SLCmd::Fold {
                        pred_name,
                        parameters: parameters.into_iter().map(|p| p.pvar_to_lvar()).collect(),
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
                ProofStep::Call { lemma_call } => {
                    let (lemma_name, parameters) =
                        pred_ctx.compile_call(lemma_call, CallerKind::Lemma);
                    let parameters = parameters.into_iter().map(|p| p.pvar_to_lvar()).collect();
                    gil_proof.push(LCmd::SL(SLCmd::ApplyLem {
                        lemma_name,
                        parameters,
                        existentials: Vec::new(),
                    }))
                }
                ProofStep::AssertBind { assertion, vars } => {
                    let assertion = pred_ctx.compile_assertion(assertion).pvar_to_lvar();
                    gil_proof.push(LCmd::SL(SLCmd::SepAssert {
                        assertion,
                        existentials: vars.iter().map(|v| format!("#{v}")).collect(),
                    }))
                }
                ProofStep::Assume { formula } => {
                    let formula = pred_ctx.compile_formula(formula).pvar_to_lvar();
                    gil_proof.push(LCmd::Assume(formula))
                }
            };
        }
        gil_proof
    }
}
