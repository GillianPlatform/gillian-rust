use rustc_ast::LitKind;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{self, interpret::Scalar, BorrowKind, ConstValue},
    thir::{self, AdtExpr, ClosureExpr, ExprId, LocalVarId, Thir},
    ty::{self, GenericArgsRef, Ty, TyCtxt, TyKind, UpvarArgs},
};

use rustc_span::Symbol;
use rustc_target::abi::{FieldIdx, VariantIdx};

use super::builtins::LogicStubs;

/// Pure logical terms, must have no spatial or resource component.
#[derive(Debug)]
pub enum ExprKind<'tcx> {
    Call {
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        args: Vec<Expr<'tcx>>,
    },
    BinOp {
        left: Box<Expr<'tcx>>,
        op: BinOp,
        right: Box<Expr<'tcx>>,
    },
    Constructor {
        def_id: DefId,
        _args: GenericArgsRef<'tcx>,
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
    Integer {
        value: u128,
    },
    // Unclear whether this is worth distinguishing in the AST or just delegating this to the backend
    SeqNil,
    SeqOp {
        op: SeqOp,
        args: Vec<Expr<'tcx>>,
    },
    ZST,
    SetProphecy {
        mut_ref: Box<Expr<'tcx>>,
        prophecy: Box<Expr<'tcx>>,
    },
    GetProphecy {
        mut_ref: Box<Expr<'tcx>>,
    },
    GetValue {
        mut_ref: Box<Expr<'tcx>>,
    },
}

#[derive(Debug)]
pub enum FormulaKind<'tcx> {
    // True,
    // False,
    FOp {
        left: Box<FormulaKind<'tcx>>,
        op: FOp,
        right: Box<FormulaKind<'tcx>>,
    },
    EOp {
        left: Box<Expr<'tcx>>,
        op: EOp,
        right: Box<Expr<'tcx>>,
    },
    Neg {
        form: Box<FormulaKind<'tcx>>,
    },
}

/// Propositional operators
#[derive(Debug)]
pub enum FOp {
    Impl,
    Or,
    And,
}

/// Expression operations
#[derive(Debug)]
#[allow(dead_code)]
pub enum EOp {
    Lt,
    Le,
    Eq,
    Ne,
    SetMem,
    SetSub,
}

#[derive(Debug)]
pub enum SeqOp {
    Append,
    Prepend,
    Concat,
    Head,
    Tail,
    Len,
    At,
    Sub,
    Repeat,
}

#[derive(Debug)]
#[allow(dead_code)]
pub enum BinOp {
    Eq,
    Lt,
    Le,
    Ne,
    Sub,
    Add,
}

#[derive(Debug)]
pub struct Formula<'tcx> {
    pub bound_vars: Vec<(Symbol, Ty<'tcx>)>,
    pub body: FormulaKind<'tcx>,
}

#[derive(Debug)]
pub struct Expr<'tcx> {
    pub kind: ExprKind<'tcx>,
    pub ty: Ty<'tcx>,
}

#[derive(Debug)]
pub struct Assert<'tcx> {
    pub kind: AssertKind<'tcx>,
}

#[derive(Debug)]
pub enum AssertKind<'tcx> {
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
    Observation {
        formula: Formula<'tcx>,
    },
    ProphecyController {
        prophecy: Expr<'tcx>,
        model: Expr<'tcx>,
    },
    ProphecyObserver {
        prophecy: Expr<'tcx>,
        model: Expr<'tcx>,
    },
    PointsToSlice {
        src: Expr<'tcx>,
        size: Expr<'tcx>,
        pointees: Expr<'tcx>,
    },
    Uninit {
        pointer: Expr<'tcx>,
    },
    ManyUninits {
        pointer: Expr<'tcx>,
        size: Expr<'tcx>,
    },
    MaybeUninit {
        pointer: Expr<'tcx>,
        pointee: Expr<'tcx>,
    },
    ManyMaybeUninits {
        pointer: Expr<'tcx>,
        pointees: Expr<'tcx>,
        size: Expr<'tcx>,
    },
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
                    Some(LogicStubs::AssertObservation) => {
                        let formula = self.build_formula(args[0]);
                        AssertKind::Observation { formula }
                    }
                    Some(LogicStubs::AssertPointsToSlice) => {
                        let src = self.build_expression(args[0]);
                        let size = self.build_expression(args[1]);
                        let pointees = self.build_expression(args[1]);

                        // TODO unify with PointsTo
                        AssertKind::PointsToSlice {
                            src,
                            size,
                            pointees,
                        }
                    }
                    Some(LogicStubs::AssertUninit) => {
                        let pointer = self.build_expression(args[0]);

                        AssertKind::Uninit { pointer }
                    }
                    Some(LogicStubs::AssertManyUninits) => {
                        let pointer = self.build_expression(args[0]);

                        let size = self.build_expression(args[1]);

                        AssertKind::ManyUninits { pointer, size }
                    }
                    Some(LogicStubs::AssertMaybeUninit) => {
                        let pointer = self.build_expression(args[0]);
                        let pointee = self.build_expression(args[1]);

                        AssertKind::MaybeUninit { pointer, pointee }
                    }
                    Some(LogicStubs::AssertManyMaybeUninits) => {
                        let pointer = self.build_expression(args[0]);

                        let size = self.build_expression(args[1]);
                        let pointees = self.build_expression(args[2]);
                        AssertKind::ManyMaybeUninits {
                            pointer,
                            pointees,
                            size,
                        }
                    }
                    Some(LogicStubs::ProphecyObserver) => {
                        let prophecy = self.build_expression(args[0]);
                        let model = self.build_expression(args[1]);
                        AssertKind::ProphecyObserver { prophecy, model }
                    }
                    Some(LogicStubs::ProphecyController) => {
                        let prophecy = self.build_expression(args[0]);
                        let model = self.build_expression(args[1]);
                        AssertKind::ProphecyController { prophecy, model }
                    }
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
                    Some(LogicStubs::FormulaForall) => self.build_forall_body(args[0]),
                    _ => Formula {
                        bound_vars: Vec::new(),
                        body: self.build_formula_body(id),
                    },
                }
            }
            _ => self
                .tcx
                .dcx()
                .fatal(format!("Unsupported formula: {:?}", expr)),
        }
    }

    fn build_forall_body(&self, id: ExprId) -> Formula<'tcx> {
        match &self.thir[id].kind {
            thir::ExprKind::Scope { value, .. } => self.build_forall_body(*value),
            thir::ExprKind::Closure(box ClosureExpr {
                closure_id,
                args: UpvarArgs::Closure(args),
                ..
            }) => {
                let name = self.tcx.fn_arg_names(*closure_id)[0];
                let ty = args
                    .as_closure()
                    .sig()
                    .input(0)
                    .skip_binder()
                    .tuple_fields()[0];
                let (thir, expr) = self.tcx.thir_body(closure_id).unwrap();
                let body = Self {
                    thir: thir.borrow().clone(),
                    tcx: self.tcx,
                }
                .build_formula_body(expr);
                Formula {
                    bound_vars: vec![(name.name, ty)],
                    body,
                }
            }
            kind => self
                .tcx
                .dcx()
                .fatal(format!("Unexpected quantified form: {:?}", kind)),
        }
    }

    fn build_formula_body(&self, id: ExprId) -> FormulaKind<'tcx> {
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
            } => self.build_formula_body(*value),

            thir::ExprKind::Use { source } => self.build_formula_body(*source),
            thir::ExprKind::Call {
                ty, fun: _, args, ..
            } => {
                let stub = self.get_stub(*ty);
                match stub {
                    Some(LogicStubs::FormulaEqual) => {
                        let left = self.build_expression(args[0]);
                        let right = self.build_expression(args[1]);
                        FormulaKind::EOp {
                            left: Box::new(left),
                            op: EOp::Eq,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaLess) => {
                        let left = self.build_expression(args[0]);
                        let right = self.build_expression(args[1]);
                        FormulaKind::EOp {
                            left: Box::new(left),
                            op: EOp::Lt,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaLessEq) => {
                        let left = self.build_expression(args[0]);
                        let right = self.build_expression(args[1]);
                        FormulaKind::EOp {
                            left: Box::new(left),
                            op: EOp::Le,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaAnd) => {
                        let left = self.build_formula_body(args[0]);
                        let right = self.build_formula_body(args[1]);
                        FormulaKind::FOp {
                            left: Box::new(left),
                            op: FOp::And,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaOr) => {
                        let left = self.build_formula_body(args[0]);
                        let right = self.build_formula_body(args[1]);
                        FormulaKind::FOp {
                            left: Box::new(left),
                            op: FOp::Or,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaNeg) => {
                        let form = self.build_formula_body(args[0]);
                        FormulaKind::Neg {
                            form: Box::new(form),
                        }
                    }
                    Some(LogicStubs::FormulaNotEqual) => {
                        let left = self.build_expression(args[0]);
                        let right = self.build_expression(args[1]);
                        FormulaKind::EOp {
                            left: Box::new(left),
                            op: EOp::Ne,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaImplication) => {
                        let left = self.build_formula_body(args[0]);
                        let right = self.build_formula_body(args[1]);
                        FormulaKind::FOp {
                            left: Box::new(left),
                            op: FOp::Impl,
                            right: Box::new(right),
                        }
                    }
                    _ => self
                        .tcx
                        .dcx()
                        .fatal(format!("Unsupported formula: {:?}", expr)),
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

    fn compile_constant(&self, cst: ConstValue<'tcx>, ty: Ty<'tcx>) -> ExprKind<'tcx> {
        match (cst, ty.kind()) {
            (ConstValue::ZeroSized, _) => ExprKind::ZST,
            (ConstValue::Scalar(Scalar::Int(sci)), TyKind::Int(..)) => {
                let i = sci
                    .try_to_int(sci.size())
                    .expect("Cannot fail because we chose the right size");
                ExprKind::Integer { value: i as u128 }
            }
            (ConstValue::Scalar(Scalar::Int(sci)), TyKind::Uint(..)) => {
                let i = sci
                    .try_to_uint(sci.size())
                    .expect("Cannot fail because we chose the right size");
                ExprKind::Integer { value: i }
            }
            _ => self
                .tcx
                .dcx()
                .fatal(format!("Cannot encore constant {:?} of type {:?}", cst, ty)),
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
            thir::ExprKind::NamedConst {
                def_id,
                args,
                user_ty: _,
            } => {
                if !args.is_empty() {
                    self.tcx
                        .dcx()
                        .fatal(format!("Cannot evaluate this constant yet: {:?}", def_id));
                };
                let cst = self.tcx.const_eval_poly(*def_id).unwrap_or_else(|_| {
                    self.tcx
                        .dcx()
                        .fatal(format!("Cannot evaluate this constant yet: {:?}", def_id))
                });

                self.compile_constant(cst, expr.ty)
            }
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
                    _args: args,
                    variant_index: *variant_index,
                    fields,
                }
            }
            thir::ExprKind::Tuple { fields } => {
                let fields = fields.iter().map(|f| self.build_expression(*f)).collect();

                ExprKind::Tuple { fields }
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
            thir::ExprKind::Literal { lit, neg: false } => match lit.node {
                LitKind::Int(i, _) => ExprKind::Integer { value: i.get() },
                _ => self
                    .tcx
                    .dcx()
                    .fatal(format!("Unsupported literal {:?}", expr)),
            },
            thir::ExprKind::Field {
                lhs,
                variant_index: _,
                name,
            } => {
                let lhs = self.build_expression(*lhs);
                ExprKind::Field {
                    lhs: Box::new(lhs),
                    field: *name,
                }
            }
            thir::ExprKind::Binary { op, lhs, rhs } => {
                let lhs = self.build_expression(*lhs);

                let rhs = self.build_expression(*rhs);
                let op = match op {
                    mir::BinOp::Sub => BinOp::Sub,
                    _ => todo!(),
                };

                ExprKind::BinOp {
                    left: Box::new(lhs),
                    op,
                    right: Box::new(rhs),
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

                        ExprKind::BinOp {
                            left,
                            op: BinOp::Eq,
                            right,
                        }
                    }
                    Some(LogicStubs::FormulaLessEq) => {
                        assert!(args.len() == 2, "Equal call must have two arguments");
                        let left = Box::new(self.build_expression(args[0]));
                        let right = Box::new(self.build_expression(args[1]));

                        ExprKind::BinOp {
                            left,
                            op: BinOp::Le,
                            right,
                        }
                    }
                    Some(LogicStubs::FormulaLess) => {
                        assert!(args.len() == 2, "Equal call must have two arguments");
                        let left = Box::new(self.build_expression(args[0]));
                        let right = Box::new(self.build_expression(args[1]));

                        ExprKind::BinOp {
                            left,
                            op: BinOp::Lt,
                            right,
                        }
                    }
                    Some(LogicStubs::SeqNil) => ExprKind::SeqNil,
                    Some(
                        a @ (LogicStubs::SeqAppend
                        | LogicStubs::SeqPrepend
                        | LogicStubs::SeqConcat
                        | LogicStubs::SeqHead
                        | LogicStubs::SeqTail
                        | LogicStubs::SeqLen
                        | LogicStubs::SeqAt
                        | LogicStubs::SeqSub
                        | LogicStubs::SeqRepeat),
                    ) => {
                        let args = args.iter().map(|a| self.build_expression(*a)).collect();
                        let op = match a {
                            LogicStubs::SeqAppend => SeqOp::Append,
                            LogicStubs::SeqPrepend => SeqOp::Prepend,
                            LogicStubs::SeqConcat => SeqOp::Concat,
                            LogicStubs::SeqHead => SeqOp::Head,
                            LogicStubs::SeqTail => SeqOp::Tail,
                            LogicStubs::SeqLen => SeqOp::Len,
                            LogicStubs::SeqAt => SeqOp::At,
                            LogicStubs::SeqSub => SeqOp::Sub,
                            LogicStubs::SeqRepeat => SeqOp::Repeat,
                            _ => unreachable!(),
                        };
                        ExprKind::SeqOp { op, args }
                    }
                    None => {
                        let ty::FnDef(def_id, substs) = *ty.kind() else {
                            unreachable!()
                        };

                        let args = args.iter().map(|a| self.build_expression(*a)).collect();

                        ExprKind::Call {
                            def_id,
                            substs,
                            args,
                        }
                    }
                    Some(LogicStubs::MutRefGetProphecy) => {
                        // self.assert_prophecies_enabled("using `Prophecised::prophecy`");
                        let mut_ref = Box::new(self.build_expression(args[0]));
                        ExprKind::GetProphecy { mut_ref }
                    }
                    Some(LogicStubs::ProphecyGetValue) => {
                        // self.assert_prophecies_enabled("using `Prophecised::prophecy`");
                        let mut_ref = Box::new(self.build_expression(args[0]));
                        ExprKind::GetValue { mut_ref }
                    }
                    Some(LogicStubs::MutRefSetProphecy) => {
                        // self.asser/t_prophecies_enabled("using `Prophecised::assign`");
                        let mut_ref = Box::new(self.build_expression(args[0]));
                        let prophecy = Box::new(self.build_expression(args[1]));
                        ExprKind::SetProphecy { mut_ref, prophecy }
                    }
                    Some(a) => self
                        .tcx
                        .dcx()
                        .fatal(format!("{:?} unsupported stub in expression", a)),
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
}
