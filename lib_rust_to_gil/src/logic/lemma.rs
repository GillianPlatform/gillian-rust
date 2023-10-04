use super::predicate::PredCtx;
use super::utils::get_thir;
use super::LogicItem;
use gillian::gil::{Assertion, Expr, LCmd, Lemma, SLCmd};
use rustc_hir::def_id::DefId;
use rustc_middle::thir::{Param, Pat, PatKind};
use rustc_middle::ty::{AdtDef, TyCtxt, WithOptConstParam};

use crate::codegen::typ_encoding::lifetime_param_name;
use crate::temp_gen::TempGenerator;
use crate::utils::polymorphism::HasGenericLifetimes;
use crate::{
    codegen::typ_encoding::type_param_name,
    codegen::{genv::GlobalEnv, typ_encoding::TypeEncoder},
    prelude::{fatal, HasDefId, HasTyCtxt},
    utils::polymorphism::HasGenericArguments,
};

struct LemmaSig {
    name: String,
    params: Vec<String>,
}

pub(crate) struct LemmaCtx<'tcx, 'genv> {
    tcx: TyCtxt<'tcx>,
    global_env: &'genv mut GlobalEnv<'tcx>,
    did: DefId,
    temp_gen: &'genv mut TempGenerator,
    trusted: bool,
    is_extract_lemma: bool,
}

impl<'tcx, 'genv> HasTyCtxt<'tcx> for LemmaCtx<'tcx, 'genv> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl HasDefId for LemmaCtx<'_, '_> {
    fn did(&self) -> DefId {
        self.did
    }
}

impl<'tcx> HasGenericArguments<'tcx> for LemmaCtx<'tcx, '_> {}
impl<'tcx> HasGenericLifetimes<'tcx> for LemmaCtx<'tcx, '_> {}

impl<'tcx, 'genv> TypeEncoder<'tcx> for LemmaCtx<'tcx, 'genv> {
    fn add_adt_to_genv(&mut self, def: AdtDef<'tcx>) {
        self.global_env.add_adt(def);
    }

    fn adt_def_name(&self, def: &AdtDef) -> String {
        self.tcx.item_name(def.did()).to_string()
    }
}

impl<'tcx, 'genv> LemmaCtx<'tcx, 'genv> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        global_env: &'genv mut GlobalEnv<'tcx>,
        did: DefId,
        temp_gen: &'genv mut TempGenerator,
        trusted: bool,
        is_extract_lemma: bool,
    ) -> Self {
        Self {
            tcx,
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
        self.tcx.def_path_str(self.did)
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

            let wand_pre = {
                let pre_name = crate::utils::attrs::get_pre_id(self.did, self.tcx())
                    .unwrap_or_else(|| fatal!(self, "No precondition found for extract lemma"));
                let pre_did = self
                    .tcx()
                    .get_diagnostic_item(pre_name)
                    .unwrap_or_else(|| fatal!(self, "couldn't find pre-condition {}", pre_name));

                PredCtx::new(self.tcx(), self.global_env, self.temp_gen, pre_did, false)
                    .into_inner_of_borrow_call(name.clone() + "$$wand_pre")
            };
            let pre_call = (
                wand_pre.name.clone(),
                wand_pre
                    .params
                    .iter()
                    .map(|x| Expr::PVar(x.0.clone()))
                    .collect(),
            );
            res.push(LogicItem::Pred(wand_pre));

            let wand_post = {
                let post_name = crate::utils::attrs::get_post_id(self.did, self.tcx())
                    .unwrap_or_else(|| fatal!(self, "No precondition found for extract lemma"));
                let post_did = self
                    .tcx()
                    .get_diagnostic_item(post_name)
                    .unwrap_or_else(|| fatal!(self, "couldn't find pre-condition {}", post_name));

                PredCtx::new(self.tcx(), self.global_env, self.temp_gen, post_did, false)
                    .into_inner_of_borrow_call(name.clone() + "$$wand_post")
            };

            let post_call = (
                wand_post.name.clone(),
                wand_post
                    .params
                    .iter()
                    .map(|x| Expr::PVar(x.0.clone()))
                    .collect(),
            );
            res.push(LogicItem::Pred(wand_post));

            let proof = Some(vec![LCmd::SL(SLCmd::Package {
                lhs: pre_call.clone(),
                rhs: post_call.clone(),
            })]);

            // This skips the lifetime argument.
            let params = sig.params.iter().skip(1).map(Clone::clone).collect();
            let proof_lemma = Lemma {
                name,
                params,
                hyp: Assertion::pred_call_of_tuple(pre_call.clone()),
                concs: vec![Assertion::pred_call_of_tuple(post_call.clone())
                    .star(Assertion::wand(pre_call, post_call))],
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
