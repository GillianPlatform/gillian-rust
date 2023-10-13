use super::traits::TraitSolver;
use super::utils::get_thir;
use super::{builtins::Stubs, predicate::PredCtx};
use crate::prelude::*;
use gillian::gil::visitors::GilVisitor;
use gillian::gil::{Assertion, Pred};

use rustc_middle::thir::{ExprId, ExprKind, Thir};

struct ContainsPVarVisitor<'a> {
    pvar: &'a str,
    found: bool,
}

impl<'a> ContainsPVarVisitor<'a> {
    fn new(pvar: &'a str) -> Self {
        Self { pvar, found: false }
    }
}

impl<'a> GilVisitor for ContainsPVarVisitor<'a> {
    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::PVar(pvar) => {
                self.found |= pvar == self.pvar;
            }
            _ => self.super_expr(expr),
        }
    }
}

fn contains_pvar(asrt: &Assertion, pvar: &str) -> bool {
    let mut visitor = ContainsPVarVisitor::new(pvar);
    visitor.visit_assertion(asrt);
    visitor.found
}

impl<'tcx, 'genv> PredCtx<'tcx, 'genv> {
    fn check_only_pure(&self, e: ExprId, thir: &Thir<'tcx>) -> bool {
        let e = Self::resolve(e, thir);
        let expr = &thir[e];
        match &expr.kind {
            ExprKind::Call { ty, args, .. } => match self.get_stub(*ty) {
                Some(Stubs::AssertEmp | Stubs::AssertPure) => true,
                Some(Stubs::AssertStar) => {
                    self.check_only_pure(args[0], thir) && self.check_only_pure(args[1], thir)
                }
                _ => false,
            },
            _ => fatal!(self, "Unexpected assertion: {:?}", expr),
        }
    }

    fn separate_pred_and_pure(&self, e: ExprId, thir: &Thir<'tcx>) -> (ExprId, Vec<ExprId>) {
        let e: ExprId = Self::resolve(e, thir);
        let expr = &thir[e];
        match &expr.kind {
            ExprKind::Call { ty, args, .. } => match self.get_stub(*ty) {
                Some(Stubs::OwnPred) | None => (e, vec![]),
                Some(Stubs::AssertStar) => {
                    let el = args[0];
                    let er = args[1];
                    let (ell, mut ers) = self.separate_pred_and_pure(el, thir);
                    let exprl = &thir[ell];
                    if !self.check_only_pure(er, thir) {
                        fatal!(
                            self,
                            "Not well-formed extract_lemma! Side cond isn't pure: {:?}",
                            &thir[er]
                        );
                    };
                    match &exprl.kind {
                        ExprKind::Call { ty, .. }
                            if matches!(self.get_stub(*ty), Some(Stubs::OwnPred) | None) =>
                        {
                            ers.push(er);
                            (ell, ers)
                        }
                        _ => fatal!(self, "Not well-formed extract_lemma! Cannot compile, left isn't predicate: {:?}", exprl),
                    }
                }
                _ => fatal!(self, "Canot separate pred and pure: {:?}", expr),
            },
            _ => fatal!(self, "Canot separate pred and pure: {:?}", expr),
        }
    }

    pub fn compile_inner_pred_call_for_extract_lemma<'a>(
        &'a mut self,
        e: ExprId,
        thir: &'a Thir<'tcx>,
        allow_pure_side: bool,
    ) -> Assertion {
        let (e, pure) = self.separate_pred_and_pure(e, thir);
        if !(pure.is_empty() || allow_pure_side) {
            fatal!(
                self,
                "Pure side condition not allowed in post of extract lemma"
            )
        }
        for e in pure {
            let pure = self.compile_assertion(e, thir);
            self.toplevel_asrts.push(pure)
        }
        let expr = &thir[e];
        match &expr.kind {
            ExprKind::Call { ty, args, .. } => match self.get_stub(*ty) {
                Some(Stubs::OwnPred) if ty_utils::is_mut_ref_of_param_ty(thir[args[0]].ty) => {
                    let name = crate::codegen::runtime::POLY_REF_MUT_OWN_INNER.to_string();
                    let mut params = Vec::with_capacity(args.len() + 1);
                    let inner_ty = ty_utils::mut_ref_inner(thir.exprs[args[0]].ty).unwrap();
                    params.push(self.encode_type(inner_ty).into());
                    for arg in args.iter() {
                        params.push(self.compile_expression(*arg, thir));
                    }
                    Assertion::Pred { name, params }
                }
                None | Some(Stubs::OwnPred) => {
                    match ty.kind() {
                        TyKind::FnDef(def_id, substs) => {
                            let arg_ty = thir.exprs[args[0]].ty;
                            let (name, substs) = {
                                if (self.tcx().is_diagnostic_item(
                                    Symbol::intern("gillian::pcy::ownable::own"),
                                    *def_id,
                                ) || self.tcx().is_diagnostic_item(
                                    Symbol::intern("gillian::ownable::own"),
                                    *def_id,
                                )) && ty_utils::is_mut_ref(arg_ty)
                                {
                                    let name = self.global_env.add_mut_ref_own(arg_ty);
                                    let inner_ty = ty_utils::mut_ref_inner(arg_ty).unwrap();
                                    // We use the subst of the own predicate for the inner type.
                                    // That is the only thing we need here.
                                    let Instance { args, .. } = self.resolve_candidate(
                                        *def_id,
                                        self.tcx().mk_args(&[inner_ty.into()]),
                                    );
                                    (name, args)
                                } else {
                                    let instance = self.resolve_candidate(*def_id, substs);
                                    let name =
                                        rustc_middle::ty::print::with_no_trimmed_paths!(self
                                            .global_env
                                            .pred_name_for_instance(instance));
                                    (name, instance.args)
                                }
                            };
                            let mut params: Vec<Expr> =
                                Vec::with_capacity(substs.len() + args.len());
                            for subst in substs.iter() {
                                if let Some(arg) = self.encode_generic_arg(subst) {
                                    params.push(arg.into());
                                }
                            }
                            for arg in args.iter() {
                                params.push(self.compile_expression(*arg, thir));
                            }
                            let inner_name = self.global_env.inner_pred(name);
                            Assertion::Pred {
                                name: inner_name,
                                params,
                            }
                        }
                        _ => fatal!(self, "Expected a function definition for predicate type"),
                    }
                }
                _ => fatal!(
                    self,
                    "extract_lemma pre/post, expected a predicate got {:?}",
                    expr
                ),
            },
            _ => fatal!(
                self,
                "extract_lemma pre/post is not just a predicate {:?}",
                expr
            ),
        }
    }

    // Returns uni/exis vars and the predicate
    pub fn into_inner_of_borrow_call(
        mut self,
        name: String,
        allow_pure_side: bool,
    ) -> (Vec<String>, Pred) {
        let sig = self.sig();
        let (thir, ret_expr) = get_thir!(self);
        let definitions = self.resolve_definitions(ret_expr, &thir);
        if !(definitions.len()) == 1 {
            fatal!(
                self,
                "Expected exactly one definition for lemma pre {:?}",
                name
            );
        }
        let definition = definitions[0];
        let block = self.resolve_block(definition, &thir);
        let pvars = self.add_block_lvars(block, &thir);
        let block = &thir[block];
        let expr = block
            .expr
            .unwrap_or_else(|| fatal!(self, "No assertion in block?"));
        let assertion =
            self.compile_inner_pred_call_for_extract_lemma(expr, &thir, allow_pure_side);
        let assertion = std::mem::take(&mut self.toplevel_asrts)
            .into_iter()
            .filter(|x| !contains_pvar(x, "ret"))
            .chain(std::iter::once(assertion))
            .collect();
        let mut params = sig.params;
        params.remove(0); // remove lifetime argument
        let ins = (0..params.len()).collect();
        let pred = Pred {
            name,
            num_params: params.len(),
            params,
            ins,
            definitions: vec![assertion],
            facts: vec![],
            guard: None,
            abstract_: false,
            pure: false,
        };
        (pvars, pred)
    }
}
