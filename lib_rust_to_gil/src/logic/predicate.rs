use std::collections::HashMap;

use super::builtins::Stubs;
use super::utils::get_thir;
use crate::{
    codegen::{
        place::{GilPlace, GilProj},
        typ_encoding::{lifetime_param_name, type_param_name},
    },
    prelude::*,
    temp_gen::TempGenerator,
    utils::polymorphism::{HasGenericArguments, HasGenericLifetimes},
};
use gillian::gil::{Assertion, Expr as GExpr, Pred, Type};
use rustc_ast::{Lit, LitKind, MacArgs, MacArgsEq, StrStyle};

use rustc_middle::{
    mir::{
        interpret::{ConstValue, Scalar},
        BinOp, BorrowKind, Field,
    },
    thir::{AdtExpr, BlockId, ExprId, ExprKind, LocalVarId, Param, Pat, PatKind, StmtKind, Thir},
    ty::{AdtDef, AdtKind, WithOptConstParam},
};

struct PredSig {
    name: String,
    params: Vec<(String, Option<Type>)>,
    ins: Vec<usize>,
    facts: Vec<Formula>,
}

pub(crate) struct PredCtx<'tcx, 'genv> {
    tcx: TyCtxt<'tcx>,
    global_env: &'genv mut GlobalEnv<'tcx>,
    temp_gen: &'genv mut TempGenerator,
    did: DefId,
    abstract_: bool,
    var_map: HashMap<LocalVarId, GExpr>,
    type_knowledge: Vec<Assertion>,
    type_info: Vec<(Expr, Type)>,
}

impl<'tcx> HasGenericArguments<'tcx> for PredCtx<'tcx, '_> {}
impl<'tcx> HasGenericLifetimes<'tcx> for PredCtx<'tcx, '_> {}

impl<'tcx, 'genv> TypeEncoder<'tcx> for PredCtx<'tcx, 'genv> {
    fn add_adt_to_genv(&mut self, def: AdtDef<'tcx>) {
        self.global_env.add_adt(def);
    }

    fn atd_def_name(&self, def: &AdtDef) -> String {
        self.tcx.item_name(def.did()).to_string()
    }
}
impl<'tcx> HasTyCtxt<'tcx> for PredCtx<'tcx, '_> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl HasDefId for PredCtx<'_, '_> {
    fn did(&self) -> DefId {
        self.did
    }
}

// FIXME: this code isn't very elegant, there should be also a "LocalLogCtx" with a reference to the thir body,
//        that would allow to not resolve everything every time. Also, it would be reused for other logic items.
impl<'tcx: 'genv, 'genv> PredCtx<'tcx, 'genv> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        global_env: &'genv mut GlobalEnv<'tcx>,
        temp_gen: &'genv mut TempGenerator,
        did: DefId,
        abstract_: bool,
    ) -> Self {
        PredCtx {
            temp_gen,
            global_env,
            tcx,
            did,
            abstract_,
            var_map: HashMap::new(),
            type_info: Vec::new(),
            type_knowledge: Vec::new(),
        }
    }

    fn new_temp(&mut self) -> String {
        self.temp_gen.fresh_lvar()
    }

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
        if str_arg.is_empty() {
            return vec![];
        }
        str_arg
            .split(',')
            .map(|s| s.parse().expect("Ins should be a list of parameter number"))
            .collect()
    }

    fn pred_name(&self) -> String {
        self.tcx.def_path_str(self.did)
    }

    fn make_is_ptr_asrt(e: GExpr) -> Assertion {
        let types = Assertion::Types(vec![
            (e.clone(), Type::ListType),
            (e.clone().lnth(0), Type::ObjectType),
            (e.clone().lnth(1), Type::ListType),
        ]);
        let size_2 = Assertion::Pure(Formula::eq(Expr::lst_len(e), Expr::int(2)));
        types.star(size_2)
    }

    fn make_is_ref_asrt(e: GExpr) -> Assertion {
        let types = Assertion::Types(vec![
            (e.clone(), Type::ListType),
            (e.clone().lnth(0), Type::ListType),
            (e.clone().lnth(1), Type::ListType),
        ]);
        let size_2 = e.clone().lst_len().eq_f(2).into();
        let first_ptr = Self::make_is_ptr_asrt(e.clone().lnth(0));
        let second_prophecy =
        // (|e[1]| == 2) * (e[1][1] == [])
        e
            .clone()
            .lst_len()
            .eq_f(2)
            .into_asrt()
            .star(e.lnth(1).lnth(1).eq_f([]).into());
        types.star(size_2).star(first_ptr).star(second_prophecy)
    }

    fn extract_param(&mut self, param: &Param<'tcx>) -> (String, Ty<'tcx>) {
        match &param.pat {
            Some(box Pat {
                kind:
                    PatKind::Binding {
                        mutability: _,
                        name,
                        var,
                        subpattern,
                        is_primary,
                        mode: _,
                        ty: _,
                    },
                ..
            }) => {
                // When memory implements mutability, the information should probably be used.
                let name = name.to_string();
                let ty = param.ty;
                if !is_primary {
                    fatal!(self, "Predicate parameters must be primary");
                }
                if subpattern.is_some() {
                    fatal!(self, "Predicate parameters cannot have subpatterns");
                }
                self.var_map.insert(*var, GExpr::PVar(name.clone()));
                if ty.is_any_ptr() {
                    let lvar = Expr::LVar(self.new_temp());
                    self.var_map.insert(*var, lvar.clone());
                    let var_eq =
                        Assertion::Pure(Formula::eq(lvar.clone(), GExpr::PVar(name.clone())));
                    let type_knowledge = if matches!(ty.kind(), TyKind::Ref(_, _, Mutability::Mut))
                    {
                        Self::make_is_ref_asrt(lvar)
                    } else {
                        Self::make_is_ptr_asrt(lvar)
                    };
                    self.type_knowledge.push(type_knowledge.star(var_eq));
                }
                (name, ty)
            }
            _ => fatal!(self, "Predicate parameters must be variables"),
        }
    }

    fn sig(&mut self) -> PredSig {
        let generic_lifetimes = self.generic_lifetimes();
        let generic_types = self.generic_types();
        let mut ins = self.get_ins();
        let generics_amount = generic_types.len() + generic_lifetimes.len();
        if generics_amount > 0 {
            // Ins known info is only about non-type params.
            // If there are generic types args,
            // we need to add the type params as ins, and offset known ins,
            // since type params are added in front.
            for i in &mut ins {
                *i += generics_amount;
            }
            for i in 0..generics_amount {
                ins.push(i)
            }
            ins.sort();
        }
        get_thir!(thir, _expr, self);
        let generic_lft_params = generic_lifetimes
            .into_iter()
            .map(|x| (lifetime_param_name(&x), None));
        let generic_type_params = generic_types
            .into_iter()
            .map(|x| (type_param_name(x.0, x.1), None));
        let arguments = thir.params.iter().map(|p| {
            let (name, _ty) = self.extract_param(p);
            (name, None)
        });
        let params: Vec<_> = generic_lft_params
            .chain(generic_type_params)
            .chain(arguments)
            .collect();
        PredSig {
            name: self.pred_name(),
            params,
            ins,
            facts: vec![],
        }
    }

    fn compile_abstract(mut self) -> Pred {
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
        super::builtins::is_assertion_ty(ty, self.tcx)
    }

    fn is_formula_ty(&self, ty: Ty<'tcx>) -> bool {
        super::builtins::is_formula_ty(ty, self.tcx)
    }

    fn get_stub(&self, ty: Ty<'tcx>) -> Option<Stubs> {
        super::builtins::get_stub(ty, self.tcx)
    }

    fn unwrap_prophecy_ty(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        match ty.kind() {
            TyKind::Adt(_, args) => args[0].expect_ty(),
            _ => fatal!(self, "Prophecy field on non-prophecy"),
        }
    }

    fn compile_constant(&self, cst: ConstValue<'tcx>, ty: Ty<'tcx>) -> GExpr {
        match (cst, ty.kind()) {
            (ConstValue::ZeroSized, _) => vec![].into(),
            (ConstValue::Scalar(Scalar::Int(sci)), TyKind::Int(..)) => {
                let i = sci
                    .try_to_int(sci.size())
                    .expect("Cannot fail because we chose the right size");
                i.into()
            }
            (ConstValue::Scalar(Scalar::Int(sci)), TyKind::Uint(..)) => {
                let i = sci
                    .try_to_uint(sci.size())
                    .expect("Cannot fail because we chose the right size");
                i.into()
            }
            _ => fatal!(self, "Cannot encore constant {:?} of type {:?}", cst, ty),
        }
    }

    fn compile_expression(&mut self, e: ExprId, thir: &Thir<'tcx>) -> GExpr {
        let expr = &thir[e];
        match &expr.kind {
            ExprKind::Scope { value, .. } => self.compile_expression(*value, thir),
            ExprKind::VarRef { id } => match self.var_map.get(id) {
                Some(var) => var.clone(),
                None => {
                    let var_id = id.0.local_id.as_usize();
                    let name = format!("#pred_lvar{}", var_id);
                    GExpr::LVar(name)
                }
            },
            ExprKind::Adt(box AdtExpr {
                adt_def: def,
                variant_index,
                fields,
                base,
                substs: _,
                user_ty: _,
            }) => {
                if base.is_some() {
                    fatal!(self, "Illegal base in logic ADT expression")
                }
                let mut fields_with_idx: Vec<(Field, GExpr)> = fields
                    .iter()
                    .map(|f| (f.name, self.compile_expression(f.expr, thir)))
                    .collect();
                fields_with_idx.sort_by(|(f1, _), (f2, _)| f1.cmp(f2));
                let fields: Vec<GExpr> = fields_with_idx.into_iter().map(|(_, e)| e).collect();
                match def.adt_kind() {
                    AdtKind::Enum => {
                        let n: GExpr = variant_index.as_u32().into();
                        vec![n, fields.into()].into()
                    }
                    AdtKind::Struct => fields.into(),
                    AdtKind::Union => {
                        fatal!(self, "Unions are not supported in logic yet")
                    }
                }
            }
            ExprKind::NamedConst {
                def_id,
                substs,
                user_ty: _,
            } => {
                if !substs.is_empty() {
                    fatal!(self, "Cannot evaluate this constant yet: {:?}", def_id);
                };
                let cst = self.tcx.const_eval_poly(*def_id).unwrap_or_else(|_| {
                    fatal!(self, "Cannot evaluate this constant yet: {:?}", def_id)
                });
                self.compile_constant(cst, expr.ty)
            }
            ExprKind::Literal { lit, neg } => {
                if *neg {
                    fatal!(self, "Negged literal? {:?}", expr)
                }
                match lit.node {
                    LitKind::Int(i, _) => i.into(),
                    _ => fatal!(self, "Unsupported literal {:?}", expr),
                }
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let left = self.compile_expression(*lhs, thir);
                let right = self.compile_expression(*rhs, thir);
                let ty = thir.exprs[*lhs].ty;
                match op {
                    BinOp::Add => {
                        if ty.is_integral() {
                            GExpr::plus(left, right)
                        } else {
                            fatal!(self, "Unsupported type for addition {:?}", ty)
                        }
                    }
                    _ => fatal!(self, "Unsupported binary operator {:?}", op),
                }
            }
            ExprKind::Tuple { fields } => {
                let fields: Vec<GExpr> = fields
                    .iter()
                    .map(|f| self.compile_expression(*f, thir))
                    .collect();
                fields.into()
            }
            ExprKind::Field {
                lhs,
                variant_index: _,
                name,
            } if matches!(&thir[*lhs].ty.kind(), TyKind::Tuple(..)) => {
                self.compile_expression(*lhs, thir).lnth(name.as_u32())
            }
            ExprKind::Borrow {
                borrow_kind: BorrowKind::Mut { .. } | BorrowKind::Shared,
                arg,
            } => {
                // We ignore reborrows, there is no temporality in expressions.
                let arg = Self::resolve(*arg, thir);
                let arg = &thir[arg];
                match arg.kind {
                    ExprKind::Deref { arg: e } => self.compile_expression(e, thir),
                    ExprKind::Field {
                        lhs,
                        variant_index: _,
                        name,
                    } => {
                        let lhs = Self::resolve(lhs, thir);
                        let lhs = &thir[lhs];
                        match lhs.kind {
                            ExprKind::Deref { arg: derefed } => {
                                // Expression is of the form `& (*derefed).field`
                                // Derefed should be a pointer, and we offset it by the field, adding the right projection.
                                let gil_derefed = self.compile_expression(derefed, thir);
                                let ty = lhs.ty;
                                let mut place = GilPlace::base(gil_derefed, ty);
                                if ty.is_enum() {
                                    panic!("enum field, need to handle")
                                }
                                place
                                    .proj
                                    .push(GilProj::Field(name.as_u32(), self.encode_type(ty)));
                                place.into_expr_ptr()
                            }
                            _ => fatal!(self, "Cannot deref this: {:?}", lhs),
                        }
                    }
                    _ => fatal!(
                        self,
                        "Unsupported borrow in assertion, borrowing: {:?}",
                        arg
                    ),
                }
            }
            ExprKind::Call {
                ty, fun: _, args, ..
            } => match self.get_stub(*ty) {
                Some(Stubs::SeqNil) => {
                    assert!(args.is_empty());
                    GExpr::EList(vec![])
                }
                Some(Stubs::SeqAppend) => {
                    assert!(args.len() == 2);
                    let list = self.compile_expression(args[0], thir);
                    let elem = self.compile_expression(args[1], thir);
                    let elem = vec![elem].into();
                    Expr::lst_concat(list, elem)
                }
                Some(Stubs::SeqPrepend) => {
                    assert!(args.len() == 2);
                    let list = self.compile_expression(args[0], thir);
                    let elem = self.compile_expression(args[1], thir);
                    let elem = vec![elem].into();
                    Expr::lst_concat(elem, list)
                }
                Some(Stubs::SeqConcat) => {
                    assert!(args.len() == 2);
                    let left = self.compile_expression(args[0], thir);
                    let right = self.compile_expression(args[1], thir);
                    Expr::lst_concat(left, right)
                }
                Some(Stubs::SeqLen) => {
                    assert!(args.len() == 1);
                    let list = self.compile_expression(args[0], thir);
                    list.lst_len()
                }
                Some(Stubs::MutRefGetProphecy) => {
                    assert!(args.len() == 1);
                    let mut_ref = self.compile_expression(args[0], thir);
                    mut_ref.lnth(1)
                }
                Some(Stubs::ProphecyGetValue) => {
                    assert!(args.len() == 1);
                    let proph = self.compile_expression(args[0], thir);
                    proph.lnth(0)
                }
                Some(Stubs::ProphecyField(i)) => {
                    assert!(args.len() == 1);
                    let proph = self.compile_expression(args[0], thir);
                    let ty = self.unwrap_prophecy_ty(thir.exprs[args[0]].ty);
                    [
                        proph.clone().lnth(0),
                        proph.lnth(1).lst_concat(
                            [GilProj::Field(i, self.encode_type(ty)).into_expr()].into(),
                        ),
                    ]
                    .into()
                }
                _ => fatal!(self, "{:?} unsupported call in expression", expr),
            },
            _ => fatal!(
                self,
                "{:?} unsupported Thir expression in expression while compiling {:?}",
                expr,
                self.did()
            ),
        }
    }

    fn compile_formula(&mut self, e: ExprId, thir: &Thir<'tcx>) -> Formula {
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
            } => {
                let stub = self.get_stub(*ty);
                match stub {
                    Some(Stubs::FormulaEqual) => {
                        assert!(args.len() == 2, "Equal call must have two arguments");
                        let left = Box::new(self.compile_expression(args[0], thir));
                        let right = Box::new(self.compile_expression(args[1], thir));
                        Formula::Eq { left, right }
                    }
                    Some(Stubs::FormulaLessEq) => {
                        assert!(args.len() == 2, "LessEq call must have two arguments");
                        let ty = thir.exprs[args[0]].ty;
                        if thir.exprs[args[0]].ty.is_integral() {
                            let left = Box::new(self.compile_expression(args[0], thir));
                            let right = Box::new(self.compile_expression(args[1], thir));
                            Formula::ILessEq { left, right }
                        } else {
                            fatal!(self, "Used <= in formula for unknown type: {}", ty);
                        }
                    }
                    Some(Stubs::FormulaLess) => {
                        assert!(args.len() == 2, "Less call must have two arguments");
                        let ty = thir.exprs[args[0]].ty;
                        if thir.exprs[args[0]].ty.is_integral() {
                            let left = Box::new(self.compile_expression(args[0], thir));
                            let right = Box::new(self.compile_expression(args[1], thir));
                            Formula::ILess { left, right }
                        } else {
                            fatal!(self, "Used < in formula for unknown type: {}", ty);
                        }
                    }
                    _ => {
                        fatal!(self, "{:?} unsupported call in formula", expr);
                    }
                }
            }
            _ => fatal!(self, "Unsupported formula: {:?}", expr),
        }
    }

    fn is_nonnull(&self, ty: Ty<'tcx>) -> bool {
        if let Some(adt_def) = ty.ty_adt_def() {
            if let "core::ptr::NonNull" | "std::ptr::NonNull" =
                self.tcx.def_path_str(adt_def.did()).as_str()
            {
                return true;
            }
        }
        false
    }

    fn make_nonnull(&self, ptr: GExpr) -> GExpr {
        [ptr].into()
    }

    fn make_box(&self, ptr: GExpr) -> GExpr {
        let non_null = self.make_nonnull(ptr);
        let phantom_data = [].into();
        let unique = [non_null, phantom_data].into();
        let global = [].into();
        [unique, global].into()
    }

    fn compile_points_to(&mut self, args: &[ExprId], thir: &Thir<'tcx>) -> Assertion {
        assert!(args.len() == 2, "Pure call must have one argument");
        // The type in the points_to is the type of the pointee.
        let ty = self.encode_type(thir.exprs[args[1]].ty);
        let left = self.compile_expression(args[0], thir);
        let right = self.compile_expression(args[1], thir);
        let left_ty = thir.exprs[args[0]].ty;
        // If the type is a box or a nonnull, we need to access its pointer.
        let (left, pfs) = if left_ty.is_box() {
            // boxes have to be block pointers
            let loc = GExpr::LVar(self.new_temp());
            let ptr: Expr = [loc.clone(), [].into()].into();
            let typing = Assertion::Types(vec![(loc, Type::ObjectType)]);
            let box_ = self.make_box(ptr.clone());
            let eq = Formula::Eq {
                left: Box::new(box_),
                right: Box::new(left),
            };
            let eq = Assertion::Pure(eq);
            let pfs = Assertion::star(typing, eq);
            (ptr, pfs)
        } else if self.is_nonnull(left_ty) {
            // FIXME: this is technically not correct,
            // we would need to annotate the pointsTo to make sure that's true.
            let loc = GExpr::LVar(self.new_temp());
            let ptr: Expr = [loc.clone(), [].into()].into();
            let typing = Assertion::Types(vec![(loc, Type::ObjectType)]);
            let non_null = self.make_nonnull(ptr.clone());
            let eq = Formula::Eq {
                left: Box::new(non_null),
                right: Box::new(left),
            };
            let eq = Assertion::Pure(eq);
            let pfs = Assertion::star(typing, eq);
            (ptr, pfs)
        } else if matches!(left_ty.kind(), TyKind::Ref(_, _, Mutability::Mut)) {
            (left.lnth(0), Assertion::Emp)
        } else {
            (left, Assertion::Emp)
        };
        Assertion::star(pfs, super::core_preds::value(left, ty, right))
    }

    fn compile_assertion(&mut self, e: ExprId, thir: &Thir<'tcx>) -> Assertion {
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
            } => match self.get_stub(*ty) {
                Some(Stubs::AssertPure) => {
                    assert!(args.len() == 1, "Pure call must have one argument");
                    let formula = self.compile_formula(args[0], thir);
                    Assertion::Pure(formula)
                }
                Some(Stubs::AssertStar) => {
                    assert!(args.len() == 2, "Pure call must have one argument");
                    let left = self.compile_assertion(args[0], thir);
                    let right = self.compile_assertion(args[1], thir);
                    Assertion::star(left, right)
                }
                Some(Stubs::AssertEmp) => {
                    assert!(args.len() == 0, "Emp call must have no arguments");
                    Assertion::Emp
                }
                Some(Stubs::AssertPointsTo) => self.compile_points_to(args, thir),
                Some(Stubs::OwnPred)
                    if matches!(thir.exprs[args[0]].ty.kind(), TyKind::Param(_)) =>
                {
                    let name = crate::codegen::runtime::POLY_OWN_PRED.to_string();
                    let mut params = Vec::with_capacity(args.len() + 1);
                    params.push(self.encode_type(thir.exprs[args[0]].ty).into());
                    for arg in args.iter() {
                        params.push(self.compile_expression(*arg, thir));
                    }
                    Assertion::Pred { name, params }
                }
                Some(Stubs::ProphecyObserver) => {
                    let prophecy = self.compile_expression(args[0], thir);
                    let typ = self.encode_type(self.unwrap_prophecy_ty(thir.exprs[args[0]].ty));
                    let model = self.compile_expression(args[1], thir);
                    super::core_preds::observer(prophecy, typ, model)
                }
                Some(Stubs::ProphecyController) => {
                    let prophecy = self.compile_expression(args[0], thir);
                    let typ = self.encode_type(self.unwrap_prophecy_ty(thir.exprs[args[0]].ty));
                    let model = self.compile_expression(args[1], thir);
                    super::core_preds::controller(prophecy, typ, model)
                }
                _ => {
                    let (def_id, substs) = match ty.kind() {
                        TyKind::FnDef(def_id, substs) => self.resolve_candidate(*def_id, substs),
                        _ => fatal!(self, "Unsupported Thir expression: {:?}", expr),
                    };
                    let name = rustc_middle::ty::print::with_no_trimmed_paths!(self
                        .tcx
                        .def_path_str(def_id));

                    let mut params = Vec::with_capacity(args.len() + substs.len());
                    for tyarg in substs.iter().filter_map(|a| self.encode_generic_arg(a)) {
                        params.push(tyarg.into())
                    }
                    for arg in args.iter() {
                        params.push(self.compile_expression(*arg, thir));
                    }
                    Assertion::Pred { name, params }
                }
            },
            _ => fatal!(self, "Can't compile assertion yet: {:?}", expr),
        }
    }

    fn resolve_block(&self, e: ExprId, thir: &Thir<'tcx>) -> BlockId {
        let expr = &thir.exprs[e];
        match &expr.kind {
            ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.resolve_block(*value, thir),
            ExprKind::Use { source } => self.resolve_block(*source, thir),
            ExprKind::Block { block, .. } => *block,
            _ => fatal!(self, "Can't resolve block: {:?}", expr),
        }
    }

    fn compile_assertion_outer(&mut self, e: ExprId, thir: &Thir<'tcx>) -> Assertion {
        let block = self.resolve_block(e, thir);
        let block = &thir.blocks[block];
        let expr = block
            .expr
            .unwrap_or_else(|| fatal!(self, "Assertion block has no expression?"));
        for stmt in block.stmts.iter() {
            // We could do additional check that the rhs is actually a call
            // to `gilogic::new_lvar()` but 🤷‍♂️.
            if let StmtKind::Let {
                pattern:
                    box Pat {
                        kind:
                            PatKind::Binding { name, var, .. }
                            | PatKind::AscribeUserType {
                                ascription: _,
                                subpattern:
                                    box Pat {
                                        kind: PatKind::Binding { name, var, .. },
                                        ..
                                    },
                            },
                        ..
                    },
                ..
            } = thir.stmts[*stmt].kind
            {
                self.var_map
                    .insert(var, GExpr::LVar(format!("#{}", name.as_str())));
            } else {
                fatal!(
                    self,
                    "Unsupported statement in assertion: {:?}",
                    thir.stmts[*stmt]
                )
            }
        }
        let inner = self.compile_assertion(expr, thir);
        let inner = self
            .type_knowledge
            .iter()
            .fold(inner, |acc, eq| Assertion::star(acc, eq.clone()));

        let with_equalities = if self.type_info.is_empty() {
            inner
        } else {
            Assertion::star(inner, Assertion::Types(self.type_info.clone()))
        };

        let generic_lifetimes = self.generic_lifetimes();
        let with_lifetime_token = if generic_lifetimes.is_empty() {
            with_equalities
        } else {
            if generic_lifetimes.len() > 1 {
                fatal!(
                    self,
                    "Multiple generic lifetimes not supported yet in specs"
                )
            };
            generic_lifetimes.iter().fold(with_equalities, |acc, lft| {
                let lft_name = lifetime_param_name(lft);
                Assertion::star(
                    acc,
                    super::core_preds::alive_lft(Expr::LVar(format!("#{lft_name}"))),
                )
            })
        };
        with_lifetime_token
    }

    fn resolve(e: ExprId, thir: &Thir<'tcx>) -> ExprId {
        let expr = &thir.exprs[e];
        match &expr.kind {
            ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => Self::resolve(*value, thir),
            ExprKind::Use { source } => Self::resolve(*source, thir),
            _ => e,
        }
    }

    fn resolve_array(&self, e: ExprId, thir: &Thir<'tcx>) -> Vec<ExprId> {
        let expr = &thir.exprs[e];
        match &expr.kind {
            ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.resolve_array(*value, thir),
            ExprKind::Use { source } => self.resolve_array(*source, thir),
            ExprKind::Block { block } => {
                let block = &thir.blocks[*block];
                if !block.stmts.is_empty() {
                    fatal!(self, "Array block has statements when resolving the main expression of a predicate")
                }
                match &block.expr {
                    Some(e) => self.resolve_array(*e, thir),
                    None => fatal!(self, "Array block has no expression when resolving the main expression of a predicate"),
                }
            }
            ExprKind::Array { fields } => fields.to_vec(),
            _ => fatal!(self, "Can't resolve array: {:?}", expr),
        }
    }

    fn resolve_definitions(&self, e: ExprId, thir: &Thir<'tcx>) -> Vec<ExprId> {
        let expr = &thir.exprs[e];
        match &expr.kind {
            ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.resolve_definitions(*value, thir),
            ExprKind::Use { source } => self.resolve_definitions(*source, thir),
            ExprKind::Block { block } => {
                let block = &thir.blocks[*block];
                if !block.stmts.is_empty() {
                    fatal!(self, "Definitions block has statements when resolving the main expression of a predicate")
                }
                match &block.expr {
                Some(e) => self.resolve_definitions(*e, thir),
                None => fatal!(self, "Definition block has no expression when resolving the main expression of a predicate"),
            }
            }
            ExprKind::Call { ty, args, .. } if self.get_stub(*ty) == Some(Stubs::PredDefs) => {
                assert!(args.len() == 1, "Defs call must have one argument");
                self.resolve_array(args[0], thir)
            }
            _ => fatal!(self, "Can't resolve array: {:?}", expr),
        }
    }

    fn compile_concrete(mut self) -> Pred {
        let PredSig {
            name,
            params,
            ins,
            facts,
        } = self.sig();
        get_thir!(thir, ret_expr, self);
        // FIXME: Use the list of statements of the main block expr
        let definitions = self
            .resolve_definitions(ret_expr, &thir)
            .iter()
            .map(|e| self.compile_assertion_outer(*e, &thir))
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
