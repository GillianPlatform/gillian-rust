use super::predicate::PredCtx;
use super::utils::get_thir;
use super::LogicItem;
use crate::prelude::*;
use gillian::gil::{Assertion, Expr, LCmd, Lemma, SLCmd};
use rustc_hir::def_id::DefId;
use rustc_middle::thir::{Param, Pat, PatKind};
use rustc_middle::ty::GenericArgs;

use crate::codegen::typ_encoding::lifetime_param_name;
use crate::temp_gen::TempGenerator;
use crate::utils::polymorphism::HasGenericLifetimes;
use crate::{
    codegen::typ_encoding::type_param_name,
    codegen::typ_encoding::TypeEncoder,
    prelude::{fatal, HasDefId, HasTyCtxt},
    utils::polymorphism::HasGenericArguments,
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

impl<'tcx> HasGenericArguments<'tcx> for LemmaCtx<'tcx, '_> {}
impl<'tcx> HasGenericLifetimes<'tcx> for LemmaCtx<'tcx, '_> {}
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
            temp_gen,
            trusted,
            is_extract_lemma,
        }
    }

    fn extract_param(&self, param: &Param<'tcx>) -> String {
        match &param.pat {
            Some(box Pat {
                kind:
                    PatKind::Binding {
                        mutability: _,
                        name,
                        var: _,
                        subpattern,
                        is_primary,
                        mode: _,
                        ty: _,
                    },
                ..
            }) => {
                if !is_primary {
                    fatal!(self, "Predicate parameters must be primary");
                }
                if subpattern.is_some() {
                    fatal!(self, "Predicate parameters cannot have subpatterns");
                }
                name.to_string()
            }
            _ => fatal!(self, "Predicate parameters must be variables"),
        }
    }

    fn lemma_name(&self) -> String {
        let args = GenericArgs::identity_for_item(self.tcx(), self.did());
        self.global_env.just_pred_name_with_args(self.did, args)
    }

    fn sig(&self) -> LemmaSig {
        let (thir, _) = get_thir!(self);
        let lft_params = self
            .generic_lifetimes()
            .into_iter()
            .map(|x| lifetime_param_name(&x));
        let type_params = self
            .generic_types()
            .into_iter()
            .map(|x| type_param_name(x.0, x.1));
        let args = thir.params.iter().map(|p| self.extract_param(p));
        let params = lft_params.chain(type_params).chain(args).collect();
        LemmaSig {
            name: self.lemma_name(),
            params,
        }
    }

    pub(crate) fn compile(self) -> Vec<LogicItem> {
        let mut res = Vec::with_capacity(1 + 3 * (self.is_extract_lemma as usize));

        let sig = self.sig();

        if self.is_extract_lemma {
            let name = sig.name.clone() + "$$extract_proof";

            let (pvars_pre, mut proof_pre) = {
                let pre_name = crate::utils::attrs::get_pre_id(self.did, self.tcx())
                    .unwrap_or_else(|| fatal!(self, "No precondition found for extract lemma"));
                let pre_did = self
                    .tcx()
                    .get_diagnostic_item(pre_name)
                    .unwrap_or_else(|| fatal!(self, "couldn't find pre-condition {}", pre_name));

                PredCtx::new_with_identity_args(self.global_env, self.temp_gen, pre_did)
                    .into_inner_of_borrow_call(name.clone() + "$$proof_pre", true)
            };

            let pre_true_vars: Vec<Expr> = proof_pre
                .params
                .iter()
                .map(|x| Expr::PVar(x.0.clone()))
                .collect();
            let mut pre_call_params = pre_true_vars;
            pre_call_params.extend(pvars_pre.iter().map(|x| Expr::LVar(format!("#{}", x))));

            let pre_call = (proof_pre.name.clone(), pre_call_params);
            // Right now the wand_pre looks like
            // `pred(+T, +x) = P(x, #y, #z), where pvars_pre is `y`, `z`.
            // We need to fix to expose the outs.
            let eqs: Assertion = pvars_pre
                .iter()
                .map(|x| {
                    Expr::PVar(x.clone())
                        .eq_f(Expr::LVar(format!("#{}", x)))
                        .into_asrt()
                })
                .collect();
            let def = proof_pre.definitions.pop().unwrap(); // There is a unique assertion in the definitions
            proof_pre.definitions.push(def.star(eqs));
            proof_pre.num_params += pvars_pre.len();
            proof_pre
                .params
                .extend(pvars_pre.into_iter().map(|x| (x, None)));

            let post_params = proof_pre.params.clone();
            res.push(LogicItem::Pred(proof_pre));

            let (_, mut proof_post) = {
                let post_name = crate::utils::attrs::get_post_id(self.did, self.tcx())
                    .unwrap_or_else(|| fatal!(self, "No precondition found for extract lemma"));
                let post_did = self
                    .tcx()
                    .get_diagnostic_item(post_name)
                    .unwrap_or_else(|| fatal!(self, "couldn't find pre-condition {}", post_name));

                PredCtx::new_with_identity_args(self.global_env, self.temp_gen, post_did)
                    .into_inner_of_borrow_call(name.clone() + "$$proof_post", false)
            };

            let post_eqs: Assertion = post_params
                .iter()
                .map(|x| {
                    Expr::PVar(x.0.clone())
                        .eq_f(Expr::LVar(format!("#{}", x.0)))
                        .into_asrt()
                })
                .collect();
            let mut def = proof_post.definitions.pop().unwrap();
            let all_subst = post_params
                .iter()
                .map(|x| (x.0.clone(), Expr::LVar(format!("#{}", x.0))))
                .collect();
            def.subst_pvar(&all_subst);
            proof_post.definitions.push(post_eqs.star(def));
            proof_post.num_params = post_params.len();
            proof_post.params = post_params;
            proof_post.ins = (0..proof_post.num_params).collect();
            // We also need to fix the wand_post to use the outs from before (and ignore the ret thing)

            let post_call: (String, Vec<_>) = (
                proof_post.name.clone(),
                proof_post
                    .params
                    .iter()
                    .map(|x| Expr::PVar(x.0.clone()))
                    .collect(),
            );
            res.push(LogicItem::Pred(proof_post));

            let proof = {
                let mut pre_call = pre_call.clone();
                pre_call.1.iter_mut().for_each(|e| e.subst_pvar(&all_subst));
                let mut post_call = post_call.clone();
                post_call
                    .1
                    .iter_mut()
                    .for_each(|e| e.subst_pvar(&all_subst));
                Some(vec![LCmd::SL(SLCmd::Package {
                    lhs: post_call,
                    rhs: pre_call,
                })])
            };

            let mut conc = Assertion::pred_call_of_tuple(post_call.clone())
                .star(Assertion::wand(post_call, pre_call.clone()));
            conc.subst_pvar(&all_subst);
            // This skips the lifetime argument.
            let params = sig.params.iter().skip(1).map(Clone::clone).collect();
            let proof_lemma = Lemma {
                name,
                params,
                hyp: Assertion::pred_call_of_tuple(pre_call),
                concs: vec![conc],
                proof,
                variant: None,
                existentials: Vec::new(),
            };
            res.push(LogicItem::Lemma(proof_lemma));
        }
        if self.trusted {
            // We set temporary hyp and conclusion, which we be replaced later by the specs
            let lemma = Lemma {
                name: sig.name.clone(),
                params: sig.params,
                hyp: Assertion::Emp,
                concs: Vec::new(),
                proof: None,
                variant: None,
                existentials: Vec::new(),
            };
            res.push(LogicItem::Lemma(lemma));
        } else {
            fatal!(self, "Can't compile untrusted lemmas yet")
        }
        res
    }
}
