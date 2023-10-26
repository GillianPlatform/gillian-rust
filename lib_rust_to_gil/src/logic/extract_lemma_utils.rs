use super::param_collector;
use super::utils::get_thir;
use super::{builtins::LogicStubs, predicate::PredCtx};
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
                Some(LogicStubs::AssertEmp | LogicStubs::AssertPure) => true,
                Some(LogicStubs::AssertStar) => {
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
                Some(LogicStubs::OwnPred) | None => (e, vec![]),
                Some(LogicStubs::AssertStar) => {
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
                            if matches!(self.get_stub(*ty), Some(LogicStubs::OwnPred) | None) =>
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
            self.global_toplevel_asrts.push(pure)
        }
        let expr = &thir[e];
        match &expr.kind {
            ExprKind::Call { ty, args, .. } => match ty.kind() {
                TyKind::FnDef(def_id, substs) => {
                    let (name, substs) = self
                        .global_env_mut()
                        .resolve_inner_of_predicate(*def_id, substs);
                    let ty_params = param_collector::collect_params_on_args(substs)
                        .with_consider_arguments(args.iter().map(|id| thir[*id].ty));
                    let mut params = Vec::with_capacity(ty_params.parameters.len() + args.len());
                    for tyarg in ty_params.parameters {
                        let tyarg = self.encode_type(tyarg);
                        params.push(tyarg.into());
                    }
                    for arg in args.iter() {
                        params.push(self.compile_expression(*arg, thir));
                    }
                    Assertion::Pred { name, params }
                }
                _ => fatal!(self, "Expected a function definition for predicate type"),
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
        let assertion = std::mem::take(&mut self.global_toplevel_asrts)
            .into_iter()
            .chain(std::mem::take(&mut self.local_toplevel_asrts))
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
