use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BorrowKind, Place},
    thir::{self, AdtExpr, ExprId, LocalVarId, Thir},
    ty::{self, GenericArgsRef, Ty, TyCtxt},
};
use rustc_span::Symbol;
use rustc_target::abi::{FieldIdx, VariantIdx};

use super::builtins::LogicStubs;

/// Pure logical terms, must have no spatial or resource component.
#[derive(Debug)]
enum ExprKind<'tcx> {
    Call {
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        args: Vec<Expr<'tcx>>,
    },

    Eq {
        left: Box<Expr<'tcx>>,
        right: Box<Expr<'tcx>>,
    },
    Constructor {
        def_id: DefId,
        args: GenericArgsRef<'tcx>,
        fields: Vec<Expr<'tcx>>,
        variant_index: VariantIdx,
    },
    Tuple {
        fields: Vec<Expr<'tcx>>,
    },
    Field {
        lhs: Box<Expr<'tcx>>,
        field: FieldIdx,
    },
    Var {
        id: LocalVarId,
    },
}

#[derive(Debug)]
struct Formula<'tcx> {
    bound_vars: Vec<(Symbol, Ty<'tcx>)>,
    body: Expr<'tcx>,
}

#[derive(Debug)]
struct Expr<'tcx> {
    kind: ExprKind<'tcx>,
    ty: Ty<'tcx>,
}

#[derive(Debug)]
pub struct Assert<'tcx> {
    kind: AssertKind<'tcx>,
}

#[derive(Debug)]
enum AssertKind<'tcx> {
    /// Separating conjunction
    Star {
        left: Box<Assert<'tcx>>,
        right: Box<Assert<'tcx>>,
    },
    /// Pure expressions: includes constructors for types, pure logic functions etc...
    Formula {
        formula: Formula<'tcx>,
    },
    /// Predicate calls
    Call {
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        args: Vec<Expr<'tcx>>,
    },
    /// Rust Points to predicate
    PointsTo {
        // TODO(xavier): Should probably be a Place, but that requires building the places first.
        src: Expr<'tcx>,
        tgt: Expr<'tcx>,
    },
    Emp,
    // ... other core predicates
}

pub struct GilsoniteBuilder<'tcx> {
    thir: Thir<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> GilsoniteBuilder<'tcx> {
    pub fn new(thir: Thir<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self { thir, tcx }
    }

    pub fn build_assert(&self, expr: ExprId) -> Assert<'tcx> {
        Assert {
            kind: self.build_assert_kind(expr),
        }
    }

    fn build_assert_kind(&self, id: ExprId) -> AssertKind<'tcx> {
        let expr = &self.thir[id];
        if !self.is_assertion_ty(expr.ty) {
            self.tcx
                .dcx()
                .fatal(format!("{:?} is not the assertion type", expr.ty))
        }
        match &expr.kind {
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.build_assert_kind(*value),
            thir::ExprKind::Use { source } => self.build_assert_kind(*source),
            thir::ExprKind::Call {
                ty, fun: _, args, ..
            } => {
                match self.get_stub(*ty) {
                    Some(LogicStubs::AssertPure) => {
                        let formula = self.build_formula(args[0]);
                        AssertKind::Formula { formula }
                    }
                    Some(LogicStubs::AssertStar) => {
                        let mut args: Vec<_> = args.iter().map(|a| self.build_assert(*a)).collect();

                        AssertKind::Star {
                            left: Box::new(args.remove(0)),
                            right: Box::new(args.remove(0)),
                        }
                    }
                    Some(LogicStubs::AssertEmp) => AssertKind::Emp,
                    Some(LogicStubs::AssertPointsTo) => {
                        let src = self.build_expression(args[0]);
                        let tgt = self.build_expression(args[1]);

                        AssertKind::PointsTo { src, tgt }
                    }
                    // Other core predicates
                    Some(LogicStubs::AssertObservation) => todo!(),
                    Some(LogicStubs::AssertPointsToSlice) => todo!(),
                    Some(LogicStubs::AssertUninit) => todo!(),
                    Some(LogicStubs::AssertManyUninits) => todo!(),
                    Some(LogicStubs::AssertMaybeUninit) => todo!(),
                    Some(LogicStubs::AssertManyMaybeUninits) => todo!(),
                    Some(LogicStubs::ProphecyObserver) => todo!(),
                    Some(LogicStubs::ProphecyController) => todo!(),
                    Some(LogicStubs::OwnPred) | None => {
                        let ty::FnDef(def_id, substs) = *ty.kind() else {
                            unreachable!()
                        };

                        let args = args.iter().map(|a| self.build_expression(*a)).collect();

                        AssertKind::Call {
                            def_id,
                            substs,
                            args,
                        }
                    }
                    Some(s) => self
                        .tcx
                        .dcx()
                        .fatal(format!("Unsupported logic stub in assert {s:?}")),
                    // () => (),
                }
            }
            _ => self
                .tcx
                .dcx()
                .fatal(format!("Can't compile assertion yet: {:?}", expr)),
        }
    }

    fn get_stub(&self, ty: Ty<'tcx>) -> Option<LogicStubs> {
        LogicStubs::for_fn_def_ty(ty, self.tcx)
    }

    fn is_assertion_ty(&self, ty: Ty<'tcx>) -> bool {
        super::builtins::is_assertion_ty(ty, self.tcx)
    }

    fn is_formula_ty(&self, ty: Ty<'tcx>) -> bool {
        super::builtins::is_formula_ty(ty, self.tcx)
    }

    fn build_formula(&self, id: ExprId) -> Formula<'tcx> {
        let expr = &self.thir[id];
        if !self.is_formula_ty(expr.ty) {
            todo!()
            // fatal!(self, "{:?} is not the formula type", self.subst(expr.ty))
        }

        match &expr.kind {
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.build_formula(*value),
            thir::ExprKind::Use { source } => self.build_formula(*source),
            thir::ExprKind::Call {
                ty, fun: _, args, ..
            } => {
                let stub = self.get_stub(*ty);
                match stub {
                    Some(LogicStubs::FormulaForall) => todo!(),
                    _ => Formula {
                        bound_vars: Vec::new(),
                        body: self.build_expression(id),
                    },
                }
            }
            _ => self
                .tcx
                .dcx()
                .fatal(format!("Unsupported formula: {:?}", expr)),
        }
    }

    fn build_expression(&self, id: ExprId) -> Expr<'tcx> {
        Expr {
            ty: self.thir[id].ty,
            kind: self.build_expression_kind(id),
        }
    }

    fn build_expression_kind(&self, id: ExprId) -> ExprKind<'tcx> {
        let expr = &self.thir[id];

        match &expr.kind {
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.build_expression_kind(*value),
            thir::ExprKind::Use { source } => self.build_expression_kind(*source),
            thir::ExprKind::UpvarRef { var_hir_id, .. } => ExprKind::Var { id: *var_hir_id },
            thir::ExprKind::VarRef { id } => ExprKind::Var { id: *id },
            thir::ExprKind::Adt(box AdtExpr {
                adt_def,
                variant_index,
                fields,
                args,
                base,
                ..
            }) => {
                assert!(base.is_none());

                let mut fields_with_idx: Vec<(FieldIdx, _)> = fields
                    .iter()
                    .map(|f| (f.name, self.build_expression(f.expr)))
                    .collect();
                fields_with_idx.sort_by(|(f1, _), (f2, _)| f1.cmp(f2));
                let fields: Vec<_> = fields_with_idx.into_iter().map(|(_, e)| e).collect();

                ExprKind::Constructor {
                    def_id: adt_def.did(),
                    args,
                    variant_index: *variant_index,
                    fields,
                }
            }
            thir::ExprKind::Borrow {
                borrow_kind: BorrowKind::Mut { .. } | BorrowKind::Shared,
                arg,
            } => {
                let arg = &self.thir[self.peel_scope(*arg)];

                match arg.kind {
                    thir::ExprKind::Deref { arg: e } => self.build_expression_kind(e),
                    thir::ExprKind::Field { lhs, name, .. } => {
                        let thir::ExprKind::Deref { arg } = &self.thir[self.peel_scope(lhs)].kind
                        else {
                            todo!()
                        };

                        let lhs = self.build_expression(*arg);
                        ExprKind::Field {
                            lhs: Box::new(lhs),
                            field: name,
                        }
                    }
                    _ => todo!("unsupported {arg:?}"),
                }
            }
            thir::ExprKind::Call {
                ty, fun: _, args, ..
            } => {
                let stub = self.get_stub(*ty);
                match stub {
                    Some(LogicStubs::FormulaEqual) => {
                        assert!(args.len() == 2, "Equal call must have two arguments");
                        let left = Box::new(self.build_expression(args[0]));
                        let right = Box::new(self.build_expression(args[1]));

                        ExprKind::Eq { left, right }
                    }
                    // Some(LogicStubs::FormulaNotEqual) => {
                    //     assert!(args.len() == 2, "NotEqual call must have two arguments");
                    //     let left = Box::new(self.build_expression(args[0]));
                    //     let right = Box::new(self.build_expression(args[1]));
                    //     left.eq_f(*right).fnot()
                    // }
                    // Some(LogicStubs::FormulaLessEq) => {
                    //     assert!(args.len() == 2, "LessEq call must have two arguments");
                    //     let ty = self.thir.exprs[args[0]].ty;
                    //     if ty.is_integral() {
                    //         let left = Box::new(self.build_expression(args[0]));
                    //         let right = Box::new(self.build_expression(args[1]));
                    //         Formula::ILessEq { left, right }
                    //     } else {
                    //         self.tcx
                    //             .dcx()
                    //             .fatal(format!("Used <= in formula for unknown type: {}", ty))
                    //     }
                    // }
                    // Some(LogicStubs::FormulaLess) => {
                    //     assert!(args.len() == 2, "Less call must have two arguments");
                    //     let ty = self.thir.exprs[args[0]].ty;
                    //     if ty.is_integral() {
                    //         let left = Box::new(self.build_expression(args[0]));
                    //         let right = Box::new(self.build_expression(args[1]));
                    //         Formula::ILess { left, right }
                    //     } else {
                    //         self.tcx
                    //             .dcx()
                    //             .fatal(format!("Used < in formula for unknown type: {}", ty))
                    //     }
                    // }
                    // Some(LogicStubs::FormulaAnd) => {
                    //     let left = self.build_formula(args[0]);
                    //     let right = self.build_formula(args[1]);
                    //     left.and(right)
                    // }
                    // Some(LogicStubs::FormulaOr) => {
                    //     let left = self.build_formula(args[0]);
                    //     let right = self.build_formula(args[1]);
                    //     left.or(right)
                    // }
                    // Some(LogicStubs::FormulaNeg) => {
                    //     let inner = Box::new(self.build_formula(args[0]));
                    //     Formula::Not(inner)
                    // }
                    // Some(LogicStubs::FormulaForall) => self.compile_forall(args[0]),
                    // Some(LogicStubs::FormulaImplication) => {
                    //     let left = self.build_formula(args[0]);
                    //     let right = self.build_formula(args[1]);
                    //     left.implies(right)
                    // }
                    _ => self
                        .tcx
                        .dcx()
                        .fatal(format!("{:?} unsupported call in expression", expr)),
                }
            }
            _ => self
                .tcx
                .dcx()
                .fatal(format!("Unsupported expression: {:?}", expr)),
        }
    }

    fn peel_scope(&self, e: ExprId) -> ExprId {
        let expr = &self.thir.exprs[e];
        match &expr.kind {
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.peel_scope(*value),
            thir::ExprKind::Use { source } => self.peel_scope(*source),
            _ => e,
        }
    }

    // fn expect_place(&self, args: ExprId) -> Place<'tcx> {
    //     let expr = &self.thir[args];

    //     match &expr.kind {
    //         thir::ExprKind::Scope {
    //             region_scope: _,
    //             lint_level: _,
    //             value,
    //         } => self.expect_place(*value),
    //         _ => todo!("{:?}", self.thir[args]),
    //     }
    // }
}

// struct Formula<'tcx> {

// }
