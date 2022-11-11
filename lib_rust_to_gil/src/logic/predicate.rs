use crate::prelude::*;
use gillian::gil::{Assertion, Expr as GExpr, Pred, Type};
use rustc_ast::{Lit, LitKind, MacArgs, MacArgsEq, StrStyle};
use rustc_middle::{
    thir::{ExprId, ExprKind, StmtKind, Thir},
    ty::WithOptConstParam,
};

struct PredSig {
    name: String,
    params: Vec<(String, Option<Type>)>,
    ins: Vec<usize>,
    facts: Vec<Formula>,
}

pub(crate) struct PredCtx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub did: DefId,
    pub abstract_: bool,
}

impl CanFatal for PredCtx<'_> {
    fn fatal(&self, str: &str) -> ! {
        self.tcx.sess.fatal(str)
    }
}

// FIXME: this code isn't very elegant, there should be also a "LocalLogCtx" with a reference to the thir body,
//        that would allow to not resolve everything every time. Also, it would be reused for other logic items.
impl<'tcx> PredCtx<'tcx> {
    fn get_ins(&self) -> Vec<usize> {
        let ins_attr = crate::utils::attrs::get_attr(
            self.tcx.get_attrs_unchecked(self.did),
            &["gillian", "decl", "pred_ins"],
        )
        .expect("Predicate must have an ins attribute");

        let str_arg = if let MacArgs::Eq(
            _,
            MacArgsEq::Hir(Lit {
                kind: LitKind::Str(sym, StrStyle::Cooked),
                ..
            }),
        ) = ins_attr.args
        {
            sym.as_str().to_owned()
        } else {
            self.tcx
                .sess
                .fatal("Predicate ins attribute must be a string");
        };

        str_arg
            .split(',')
            .map(|s| s.parse().expect("Ins should be a list of parameter number"))
            .collect()
    }

    fn pred_name(&self) -> String {
        self.tcx.def_path_str(self.did)
    }

    fn sig(&self) -> PredSig {
        let ins = self.get_ins();
        let sig = self.tcx.fn_sig(self.did);
        let inputs = sig.inputs();
        if !inputs.bound_vars().is_empty() {
            fatal!(self, "Predicate signature as bound regions or variables")
        };
        let params = inputs
            .skip_binder()
            .iter()
            .enumerate()
            .map(|(i, _)| (format!("pred_arg{}", i), None))
            .collect();

        PredSig {
            name: self.pred_name(),
            params,
            ins,
            facts: vec![],
        }
    }

    fn compile_abstract(self) -> Pred {
        let PredSig {
            name,
            params,
            ins,
            facts,
        } = self.sig();
        Pred {
            name,
            num_params: params.len(),
            params,
            abstract_: true,
            facts,
            definitions: vec![],
            ins,
            pure: false,
        }
    }

    fn is_assertion_ty(&self, ty: Ty<'tcx>) -> bool {
        super::builtins::is_assertion_ty(self.tcx, ty)
    }

    fn is_formula_ty(&self, ty: Ty<'tcx>) -> bool {
        super::builtins::is_formula_ty(self.tcx, ty)
    }

    fn is_call_to(&self, ty: Ty<'tcx>, name: &str) -> bool {
        // TODO: Cache the diagnostic item's type to avoid the cost of lookup every time
        // There is also probably a more direct way of doing this
        if let TyKind::FnDef(did, _) = ty.kind() {
            self.tcx.is_diagnostic_item(Symbol::intern(name), *did)
        } else {
            false
        }
    }

    fn compile_formula(&self, e: ExprId, thir: &Thir<'tcx>) -> Formula {
        let expr = &thir.exprs[e];
        if !self.is_formula_ty(expr.ty) {
            fatal!(self, "{:?} is not the formula type", expr.ty)
        }

        match &expr.kind {
            ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.compile_formula(*value, thir),
            ExprKind::Use { source } => self.compile_formula(*source, thir),
            ExprKind::Call {
                ty, fun: _, args, ..
            } if self.is_call_to(*ty, "gillian::formula::equal") => {
                // FIXME: This doesn't match because equal is polymorphic and it gets monomorphized here.
                assert!(args.len() == 2, "Equal call must have one argument");
                let left = Box::new(GExpr::int(0));
                let right = Box::new(GExpr::int(1));
                Formula::Eq { left, right }
            }
            _ => fatal!(self, "Unsupported formula: {:?}", expr),
        }
    }

    fn compile_assertion(&self, e: ExprId, thir: &Thir<'tcx>) -> Assertion {
        let expr = &thir.exprs[e];
        if !self.is_assertion_ty(expr.ty) {
            fatal!(self, "{:?} is not the assertion type", expr.ty)
        }

        match &expr.kind {
            ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.compile_assertion(*value, thir),
            ExprKind::Use { source } => self.compile_assertion(*source, thir),
            ExprKind::Call {
                ty, fun: _, args, ..
            } if self.is_call_to(*ty, "gillian::asrt::pure") => {
                assert!(args.len() == 1, "Pure call must have one argument");
                let formula = self.compile_formula(args[0], thir);
                Assertion::Pure(formula)
            }
            _ => fatal!(self, "Can't compile assertion yet: {:?}", expr),
        }
    }

    fn compile_concrete(self) -> Pred {
        let PredSig {
            name,
            params,
            ins,
            facts,
        } = self.sig();
        let (thir, _expr) = self
            .tcx
            .thir_body(WithOptConstParam::unknown(
                self.did.as_local().expect("non-local predicate"),
            ))
            .expect("Predicate body failed to typecheck");
        let thir = thir.borrow();

        // FIXME: Use the list of statements of the main block expr
        let definitions = thir
            .stmts
            .iter()
            .map(|stmt| match &stmt.kind {
                StmtKind::Let { .. } => fatal!(self, "let statement is not an assertion"),
                StmtKind::Expr { expr, .. } => self.compile_assertion(*expr, &thir),
            })
            .collect();

        Pred {
            name,
            num_params: params.len(),
            params,
            abstract_: false,
            facts,
            definitions,
            ins,
            pure: false,
        }
    }

    pub(crate) fn compile(self) -> Pred {
        if self.abstract_ {
            self.compile_abstract()
        } else {
            self.compile_concrete()
        }
    }
}
