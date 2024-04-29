use std::collections::HashMap;

use super::utils::get_thir;
use super::{builtins::LogicStubs, is_borrow};
use crate::signature::build_signature;
use crate::{
    codegen::{
        place::{GilPlace, GilProj},
        typ_encoding::{lifetime_param_name, type_param_name},
    },
    logic::{core_preds, param_collector},
    prelude::*,
    temp_gen::TempGenerator,
    utils::polymorphism::{generic_types, has_generic_lifetimes},
};
use gillian::gil::{Assertion, Expr as GExpr, Pred, Type};
use indexmap::IndexMap;
use rustc_ast::LitKind;

use rustc_middle::{
    mir::{interpret::Scalar, BinOp, BorrowKind},
    thir::{AdtExpr, BlockId, ClosureExpr, ExprId, ExprKind, LocalVarId, PatKind, Thir},
    ty::{AdtKind, EarlyBinder, UpvarArgs},
};
use rustc_target::abi::FieldIdx;
use rustc_type_ir::fold::TypeFoldable;

pub(crate) struct PredSig<'tcx> {
    pub name: String,
    pub lfts: Vec<String>,
    pub generics: Vec<String>,
    pub inputs: Vec<(String, Ty<'tcx>)>,
    pub ins: Vec<usize>,
    pub facts: Vec<Formula>,
    pub guard: Option<Assertion>,
}

pub(crate) struct PredCtx<'tcx, 'genv> {
    global_env: &'genv mut GlobalEnv<'tcx>,
    temp_gen: &'genv mut TempGenerator,
    /// Identifier of the item providing the body (aka specification).
    body_id: DefId,
    args: GenericArgsRef<'tcx>,
    var_map: HashMap<LocalVarId, GExpr>,
    local_toplevel_asrts: Vec<Assertion>, // Assertions that are local to a single definition
    lvars: IndexMap<Symbol, Ty<'tcx>>,
}

impl<'tcx> HasGlobalEnv<'tcx> for PredCtx<'tcx, '_> {
    fn global_env_mut(&mut self) -> &mut GlobalEnv<'tcx> {
        self.global_env
    }

    fn global_env(&self) -> &GlobalEnv<'tcx> {
        self.global_env
    }
}

impl<'tcx> HasTyCtxt<'tcx> for PredCtx<'tcx, '_> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.global_env.tcx()
    }
}

impl<'tcx> TypeEncoder<'tcx> for PredCtx<'tcx, '_> {}

impl<'tcx> PredSig<'tcx> {
    pub(crate) fn params(&self) -> Vec<(String, Option<Type>)> {
        self.lfts
            .iter()
            .chain(self.generics.iter())
            .chain(self.inputs.iter().map(|(nm, _)| nm))
            .cloned()
            .map(|nm| (nm, None))
            .collect()
    }
}

// FIXME: this code isn't very elegant, there should be also a "LocalLogCtx" with a reference to the thir body,
//        that would allow to not resolve everything every time. Also, it would be reused for other logic items.
impl<'tcx: 'genv, 'genv> PredCtx<'tcx, 'genv> {
    pub fn new(
        global_env: &'genv mut GlobalEnv<'tcx>,
        temp_gen: &'genv mut TempGenerator,
        body_id: DefId,
        args: GenericArgsRef<'tcx>,
    ) -> Self {
        PredCtx {
            temp_gen,
            global_env,
            body_id,
            args,
            var_map: HashMap::new(),
            local_toplevel_asrts: Vec::new(),
            lvars: Default::default(),
        }
    }

    pub fn new_with_identity_args(
        global_env: &'genv mut GlobalEnv<'tcx>,
        temp_gen: &'genv mut TempGenerator,
        body_id: DefId,
    ) -> Self {
        let args = GenericArgs::identity_for_item(global_env.tcx(), body_id);
        Self::new(global_env, temp_gen, body_id, args)
    }

    pub fn prophecies_enabled(&self) -> bool {
        self.global_env.config.prophecies
    }

    pub fn subst<F: TypeFoldable<TyCtxt<'tcx>>>(&self, foldable: F) -> F {
        EarlyBinder::bind(foldable).instantiate(self.tcx(), self.args)
    }

    pub fn encode_type_with_args(&mut self, ty: Ty<'tcx>) -> EncodedType {
        self.encode_type(self.subst(ty))
    }

    pub fn assert_prophecies_enabled(&self, msg: &str) {
        if !self.prophecies_enabled() {
            let msg = format!("Prophecies are not enabled: {}", msg);
            self.tcx().sess.fatal(msg);
        }
    }

    fn new_temp(&mut self) -> String {
        self.temp_gen.fresh_lvar()
    }

    fn temp_lvar(&mut self, ty: Ty<'tcx>) -> GExpr {
        let name = self.new_temp();

        // HACK(xavier): Fix this later once the `mk_wf_asrt` is removed;
        self.lvars.insert(Symbol::intern(&name), ty);
        Expr::LVar(name)
    }

    fn get_ins(&self) -> Vec<usize> {
        // Special case for items that are in gilogic.
        // This code yeets as soon as we can do multi-crate.

        if let Some(LogicStubs::OwnPred | LogicStubs::RefMutInner | LogicStubs::OptionOwnPred) =
            LogicStubs::of_def_id(self.body_id, self.tcx())
        {
            return vec![0];
        }

        let Some(ins_attr) = crate::utils::attrs::get_attr(
            self.tcx().get_attrs_unchecked(self.body_id),
            &["gillian", "decl", "pred_ins"],
        ) else {
            fatal!(
                self,
                "Predicate {:?} doesn't have ins attribute",
                self.pred_name()
            )
        };

        let Some(str_arg) = ins_attr.value_str() else {
            self.tcx()
                .sess
                .fatal("Predicate ins attribute must be a string")
        };
        let str_arg = str_arg.as_str().to_owned();

        if str_arg.is_empty() {
            return vec![];
        }
        str_arg
            .split(',')
            .map(|s| s.parse().expect("Ins should be a list of parameter number"))
            .collect()
    }

    pub fn pred_name(&self) -> String {
        self.global_env
            .just_pred_name_with_args(self.body_id, self.args)
    }

    fn guard(&self) -> Option<Assertion> {
        is_borrow(self.body_id, self.tcx()).then(|| {
            if !has_generic_lifetimes(self.body_id, self.tcx()) {
                fatal!(self, "Borrow without a lifetime? {:?}", self.pred_name());
            }
            core_preds::alive_lft(Expr::PVar(lifetime_param_name("a")))
        })
    }

    pub fn sig(&mut self) -> PredSig<'tcx> {
        // Get the id which describes the signature of this predicate.
        // For specifications this is the identifier of the function being specified.
        let sig_id = self
            .global_env
            .prog_map
            .get(&self.body_id)
            .cloned()
            .unwrap_or(self.body_id);

        let has_generic_lifetimes = has_generic_lifetimes(self.body_id, self.tcx());
        let generic_types = generic_types(self.body_id, self.tcx());
        let mut ins = self.get_ins();
        let generics_amount = generic_types.len() + (has_generic_lifetimes as usize);
        if generics_amount > 0 {
            // Ins known info is only about non-type params.
            // If thefre are generic types args,
            // we need to add the type params as ins, and offset known ins,
            // since type params are added in front.
            for i in &mut ins {
                *i += generics_amount;
            }
            ins.extend(0..generics_amount);
            ins.sort();
        }

        let generic_lft_params = if has_generic_lifetimes {
            Some(lifetime_param_name("a")).into_iter()
        } else {
            None.into_iter()
        };

        let generic_type_params = generic_types.into_iter().map(|x| type_param_name(x.0, x.1));

        let arguments: Vec<_> = fn_args_and_tys(self.tcx(), sig_id)
            .into_iter()
            .map(|(nm, ty)| (nm.to_string(), self.subst(ty)))
            .collect();
        let guard = self.guard();

        PredSig {
            name: self.pred_name(),
            lfts: generic_lft_params.collect(),
            generics: generic_type_params.collect(),
            inputs: arguments,
            ins,
            facts: vec![],
            guard,
        }
    }

    fn is_assertion_ty(&self, ty: Ty<'tcx>) -> bool {
        super::builtins::is_assertion_ty(ty, self.tcx())
    }

    fn is_formula_ty(&self, ty: Ty<'tcx>) -> bool {
        super::builtins::is_formula_ty(ty, self.tcx())
    }

    pub(crate) fn get_stub(&self, ty: Ty<'tcx>) -> Option<LogicStubs> {
        LogicStubs::for_fn_def_ty(ty, self.tcx())
    }

    fn unwrap_prophecy_ty(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        match ty.kind() {
            TyKind::Adt(_, args) => args[0].expect_ty(),
            _ => fatal!(self, "Prophecy field on non-prophecy"),
        }
    }

    fn compile_constant(&self, cst: ConstValue<'tcx>, ty: Ty<'tcx>) -> GExpr {
        let ty = self.subst(ty);
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

    pub(crate) fn compile_expression(&mut self, e: ExprId, thir: &Thir<'tcx>) -> GExpr {
        let expr = &thir[e];
        match &expr.kind {
            ExprKind::Scope { value, .. } => self.compile_expression(*value, thir),
            ExprKind::VarRef { id } | ExprKind::UpvarRef { var_hir_id: id, .. } => {
                match self.var_map.get(id) {
                    // Actually, the information about variable names is contained in
                    // `self.tcx().hir().name(id.0)`. So the information I keep is redundant.
                    // This deserves a cleanum.
                    Some(var) => var.clone(),
                    None => {
                        let name = format!("#{}", self.tcx().hir().name(id.0));
                        GExpr::LVar(name)
                    }
                }
            }
            ExprKind::Adt(box AdtExpr {
                adt_def: def,
                variant_index,
                fields,
                base,
                args: _,
                user_ty: _,
            }) => {
                if base.is_some() {
                    fatal!(self, "Illegal base in logic ADT expression")
                }
                let mut fields_with_idx: Vec<(FieldIdx, GExpr)> = fields
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
                args,
                user_ty: _,
            } => {
                if !args.is_empty() {
                    fatal!(self, "Cannot evaluate this constant yet: {:?}", def_id);
                };
                let cst = self.tcx().const_eval_poly(*def_id).unwrap_or_else(|_| {
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
                let ty = self.subst(thir.exprs[*lhs].ty);
                match op {
                    BinOp::Add => {
                        if ty.is_integral() {
                            GExpr::plus(left, right)
                        } else {
                            fatal!(self, "Unsupported type for addition {:?}", ty)
                        }
                    }
                    BinOp::Sub => {
                        if ty.is_integral() {
                            GExpr::minus(left, right)
                        } else {
                            fatal!(self, "Unsupported type for substraction {:?}", ty)
                        }
                    }
                    BinOp::Shl => {
                        if ty.is_integral() {
                            GExpr::i_shl(left, right)
                        } else {
                            fatal!(self, "Unsupported type for << {:?}", ty)
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
            } if matches!(self.subst(thir[*lhs].ty).kind(), TyKind::Tuple(..)) => {
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
                                let ty = self.subst(lhs.ty);
                                let mut place = GilPlace::base(gil_derefed, ty);
                                if ty.is_enum() {
                                    panic!("enum field, need to handle")
                                }
                                place.proj.push(GilProj::Field(
                                    name.as_u32(),
                                    self.encode_type_with_args(ty),
                                ));
                                if self.prophecies_enabled() {
                                    [place.into_expr_ptr(), [Expr::null(), vec![].into()].into()]
                                        .into()
                                } else {
                                    place.into_expr_ptr()
                                }
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
            ExprKind::Field {
                lhs,
                variant_index: _,
                name,
            } => match self.subst(thir[*lhs].ty).ty_adt_def() {
                Some(adt) => {
                    if adt.is_struct() {
                        let lhs = self.compile_expression(*lhs, thir);
                        lhs.lnth(name.as_usize())
                    } else {
                        fatal!(self, "Can't use field access on enums in assertions.")
                    }
                }
                None => fatal!(self, "Field access on non-adt in assertion?"),
            },
            ExprKind::Call {
                ty, fun: _, args, ..
            } => match self.get_stub(*ty) {
                Some(LogicStubs::SeqNil) => {
                    assert!(args.is_empty());
                    GExpr::EList(vec![])
                }
                Some(LogicStubs::SeqAppend) => {
                    let list = self.compile_expression(args[0], thir);
                    let elem = self.compile_expression(args[1], thir);
                    let elem = vec![elem].into();
                    Expr::lst_concat(list, elem)
                }
                Some(LogicStubs::SeqPrepend) => {
                    let list = self.compile_expression(args[0], thir);
                    let elem = self.compile_expression(args[1], thir);
                    let elem = vec![elem].into();
                    Expr::lst_concat(elem, list)
                }
                Some(LogicStubs::SeqConcat) => {
                    let left = self.compile_expression(args[0], thir);
                    let right = self.compile_expression(args[1], thir);
                    Expr::lst_concat(left, right)
                }
                Some(LogicStubs::SeqHead) => self.compile_expression(args[0], thir).lst_head(),
                Some(LogicStubs::SeqTail) => self.compile_expression(args[0], thir).lst_tail(),
                Some(LogicStubs::SeqLen) => {
                    let list = self.compile_expression(args[0], thir);
                    list.lst_len()
                }
                Some(LogicStubs::SeqAt) => {
                    let list = self.compile_expression(args[0], thir);
                    let index = self.compile_expression(args[1], thir);
                    list.lnth_e(index)
                }
                Some(LogicStubs::SeqSub) => {
                    let list = self.compile_expression(args[0], thir);
                    let start = self.compile_expression(args[1], thir);
                    let size = self.compile_expression(args[2], thir);
                    list.lst_sub_e(start, size)
                }
                Some(LogicStubs::SeqRepeat) => {
                    let elem = self.compile_expression(args[0], thir);
                    let size = self.compile_expression(args[1], thir);
                    elem.repeat(size)
                }
                Some(LogicStubs::MutRefGetProphecy) => {
                    self.assert_prophecies_enabled("using `Prophecised::prophecy`");
                    let mut_ref = self.compile_expression(args[0], thir);
                    mut_ref.lnth(1)
                }
                Some(LogicStubs::MutRefSetProphecy) => {
                    self.assert_prophecies_enabled("using `Prophecised::assign`");
                    let mut_ref = self.compile_expression(args[0], thir);
                    let pcy = self.compile_expression(args[1], thir);
                    [mut_ref.lnth(0), pcy].into()
                }
                Some(LogicStubs::ProphecyGetValue) => {
                    self.assert_prophecies_enabled("using `Prophecy::value`");
                    let prophecy = self.compile_expression(args[0], thir);
                    let ty = self.unwrap_prophecy_ty(self.subst(thir.exprs[args[0]].ty));
                    let value = self.temp_lvar(ty);
                    let ty = self.encode_type(ty);
                    self.local_toplevel_asrts.push(core_preds::pcy_value(
                        prophecy,
                        ty,
                        value.clone(),
                    ));
                    value
                }
                Some(LogicStubs::ProphecyField(i)) => {
                    self.assert_prophecies_enabled("using `Prophecy::field`");
                    let proph = self.compile_expression(args[0], thir);
                    let ty = self.unwrap_prophecy_ty(self.subst(thir.exprs[args[0]].ty));
                    [
                        proph.clone().lnth(0),
                        proph.lnth(1).lst_concat(
                            [GilProj::Field(i, self.encode_type(ty)).into_expr()].into(),
                        ),
                    ]
                    .into()
                }
                None if match ty.kind() {
                    TyKind::FnDef(def_id, _) => self.tcx().is_constructor(*def_id),
                    _ => false,
                } =>
                {
                    let fields: Vec<GExpr> = args
                        .iter()
                        .map(|a| self.compile_expression(*a, thir))
                        .collect();
                    let (did, ty_of_ctor) = match ty.kind() {
                        TyKind::FnDef(did, subst) => (
                            did,
                            self.tcx()
                                .fn_sig(*did)
                                .instantiate(self.tcx(), subst)
                                .output()
                                .skip_binder(),
                        ),
                        _ => unreachable!(),
                    };
                    let def = ty_of_ctor.ty_adt_def().unwrap();
                    if ty_of_ctor.is_enum() {
                        let idx = def.variant_index_with_ctor_id(*did).index();
                        return vec![idx.into(), fields.into()].into();
                    }
                    fatal!(self, "Constructor, but not for an enum: {:?}", expr)
                }
                None => {
                    let (did, subst) = match ty.kind() {
                        TyKind::FnDef(did, subst) => (*did, *subst),
                        _ => fatal!(self, "Not an FnDef? {:?}", ty),
                    };
                    let mut params: Vec<_> = subst
                        .iter()
                        .filter_map(|x| self.encode_generic_arg(x))
                        .map(|x| x.into())
                        .collect();
                    params.extend(args.iter().map(|e| self.compile_expression(*e, thir)));

                    let fn_sig = ty.fn_sig(self.tcx());
                    let out = fn_sig.output().skip_binder();
                    let out_var = self.temp_lvar(out);
                    params.push(out_var.clone());

                    let pred_call = Assertion::Pred {
                        name: self.tcx().def_path_str(did),
                        params,
                    };

                    self.local_toplevel_asrts.push(pred_call);
                    out_var
                }
                _ => fatal!(self, "{:?} unsupported call in expression", expr),
            },
            _ => fatal!(
                self,
                "{:?} unsupported Thir expression in expression while compiling {:?}",
                expr,
                self.body_id
            ),
        }
    }

    fn compile_forall(&mut self, e: ExprId, thir: &Thir<'tcx>) -> Formula {
        match &thir[e].kind {
            ExprKind::Scope { value, .. } => self.compile_forall(*value, thir),
            ExprKind::Closure(box ClosureExpr {
                closure_id,
                args: UpvarArgs::Closure(args),
                ..
            }) => {
                let name = self.tcx().fn_arg_names(*closure_id)[0];
                let ty = args
                    .as_closure()
                    .sig()
                    .input(0)
                    .skip_binder()
                    .tuple_fields()[0];
                let inner =
                    PredCtx::new(self.global_env, self.temp_gen, closure_id.to_def_id(), args)
                        .compile_formula_closure();
                let type_ = if ty.is_integral() {
                    Some(Type::IntType)
                } else {
                    None
                };
                Formula::forall((format!("#{}", name), type_), inner)
            }
            kind => fatal!(self, "Unexpected quantified form: {:?}", kind),
        }
    }

    fn compile_formula(&mut self, e: ExprId, thir: &Thir<'tcx>) -> Formula {
        let expr = &thir.exprs[e];
        if !self.is_formula_ty(self.subst(expr.ty)) {
            fatal!(self, "{:?} is not the formula type", self.subst(expr.ty))
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
                    Some(LogicStubs::FormulaEqual) => {
                        assert!(args.len() == 2, "Equal call must have two arguments");
                        let left = Box::new(self.compile_expression(args[0], thir));
                        let right = Box::new(self.compile_expression(args[1], thir));
                        left.eq_f(*right)
                    }
                    Some(LogicStubs::FormulaNotEqual) => {
                        assert!(args.len() == 2, "NotEqual call must have two arguments");
                        let left = Box::new(self.compile_expression(args[0], thir));
                        let right = Box::new(self.compile_expression(args[1], thir));
                        left.eq_f(*right).fnot()
                    }
                    Some(LogicStubs::FormulaLessEq) => {
                        assert!(args.len() == 2, "LessEq call must have two arguments");
                        let ty = self.subst(thir.exprs[args[0]].ty);
                        if ty.is_integral() {
                            let left = Box::new(self.compile_expression(args[0], thir));
                            let right = Box::new(self.compile_expression(args[1], thir));
                            Formula::ILessEq { left, right }
                        } else {
                            fatal!(self, "Used <= in formula for unknown type: {}", ty)
                        }
                    }
                    Some(LogicStubs::FormulaLess) => {
                        assert!(args.len() == 2, "Less call must have two arguments");
                        let ty = self.subst(thir.exprs[args[0]].ty);
                        if ty.is_integral() {
                            let left = Box::new(self.compile_expression(args[0], thir));
                            let right = Box::new(self.compile_expression(args[1], thir));
                            Formula::ILess { left, right }
                        } else {
                            fatal!(self, "Used < in formula for unknown type: {}", ty)
                        }
                    }
                    Some(LogicStubs::FormulaAnd) => {
                        let left = self.compile_formula(args[0], thir);
                        let right = self.compile_formula(args[1], thir);
                        left.and(right)
                    }
                    Some(LogicStubs::FormulaOr) => {
                        let left = self.compile_formula(args[0], thir);
                        let right = self.compile_formula(args[1], thir);
                        left.or(right)
                    }
                    Some(LogicStubs::FormulaNeg) => {
                        let inner = Box::new(self.compile_formula(args[0], thir));
                        Formula::Not(inner)
                    }
                    Some(LogicStubs::FormulaForall) => self.compile_forall(args[0], thir),
                    Some(LogicStubs::FormulaImplication) => {
                        let left = self.compile_formula(args[0], thir);
                        let right = self.compile_formula(args[1], thir);
                        left.implies(right)
                    }
                    _ => {
                        fatal!(self, "{:?} unsupported call in formula", expr)
                    }
                }
            }
            _ => fatal!(self, "Unsupported formula: {:?}", expr),
        }
    }

    fn is_nonnull(&self, ty: Ty<'tcx>) -> bool {
        crate::utils::ty::is_nonnull(ty, self.tcx())
    }

    fn make_nonnull(&self, ptr: GExpr) -> GExpr {
        [ptr].into()
    }

    fn make_box(&self, ptr: GExpr) -> GExpr {
        let non_null = self.make_nonnull(ptr);
        let phantom_data = vec![].into();
        let unique: GExpr = [non_null, phantom_data].into();
        let global = vec![].into();
        [unique, global].into()
    }

    fn compile_uninit(
        &mut self,
        args: &[ExprId],
        fn_def_ty: Ty<'tcx>,
        thir: &Thir<'tcx>,
    ) -> Assertion {
        let ty = match fn_def_ty.kind() {
            TyKind::FnDef(_, substs) => substs[1].expect_ty(),
            _ => panic!("compile_uninit went wrong"),
        };

        let pointer = self.compile_expression(args[0], thir);
        let typ = self.encode_type_with_args(ty);

        super::core_preds::uninit(pointer, typ)
    }

    fn compile_many_uninits(
        &mut self,
        args: &[ExprId],
        fn_def_ty: Ty<'tcx>,
        thir: &Thir<'tcx>,
    ) -> Assertion {
        let ty = match fn_def_ty.kind() {
            TyKind::FnDef(_, substs) => substs[1].expect_ty(),
            _ => panic!("compile_uninit went wrong"),
        };

        let pointer = self.compile_expression(args[0], thir);
        let size = self.compile_expression(args[1], thir);
        let typ = self.encode_type_with_args(ty);

        super::core_preds::many_uninits(pointer, typ, size)
    }

    fn compile_many_maybe_uninits(
        &mut self,
        args: &[ExprId],
        fn_def_ty: Ty<'tcx>,
        thir: &Thir<'tcx>,
    ) -> Assertion {
        let ty = match fn_def_ty.kind() {
            TyKind::FnDef(_, substs) => substs.last().unwrap().expect_ty(),
            _ => panic!("compile_many_maybe_uninits went wrong"),
        };
        let pointer = self.compile_expression(args[0], thir);
        let size = self.compile_expression(args[1], thir);
        let pointee = self.compile_expression(args[2], thir);
        let typ = self.encode_type_with_args(ty);
        super::core_preds::many_maybe_uninits(pointer, typ, size, pointee)
    }

    fn compile_maybe_uninit(
        &mut self,
        args: &[ExprId],
        fn_def_ty: Ty<'tcx>,
        thir: &Thir<'tcx>,
    ) -> Assertion {
        let ty = match fn_def_ty.kind() {
            TyKind::FnDef(_, substs) => substs.last().unwrap().expect_ty(),
            _ => panic!("compile_uninit went wrong"),
        };
        let ty = self.encode_type_with_args(ty);
        let pointer = self.compile_expression(args[0], thir);
        let pointee = self.compile_expression(args[1], thir);

        super::core_preds::maybe_uninit(pointer, ty, pointee)
    }

    fn compile_points_to_slice(
        &mut self,
        args: &[ExprId],
        fn_def_ty: Ty<'tcx>,
        thir: &Thir<'tcx>,
    ) -> Assertion {
        let ty = match fn_def_ty.kind() {
            TyKind::FnDef(_, substs) => substs.last().unwrap().expect_ty(),
            _ => panic!("compile points_to_slice wentwrong"),
        };
        let pointer = self.compile_expression(args[0], thir);
        let size = self.compile_expression(args[1], thir);
        let pointees = self.compile_expression(args[2], thir);

        let typ = self.encode_array_type(self.subst(ty), size);
        super::core_preds::value(pointer, typ, pointees)
    }

    fn compile_points_to(&mut self, args: &[ExprId], thir: &Thir<'tcx>) -> Assertion {
        assert!(args.len() == 2, "Pure call must have one argument");
        // The type in the points_to is the type of the pointee.
        let ty = self.encode_type_with_args(thir.exprs[args[1]].ty);
        let left = self.compile_expression(args[0], thir);
        let right = self.compile_expression(args[1], thir);
        let left_ty = self.subst(thir.exprs[args[0]].ty);
        // If the type is a box or a nonnull, we need to access its pointer.
        let (left, pfs) = if left_ty.is_box() {
            // boxes have to be block pointers.
            // We don't have that at the moment however, we need to encode
            // The idea of a "freeable" resource.
            let loc = GExpr::LVar(self.new_temp());
            let proj = GExpr::LVar(self.new_temp());
            let ptr: Expr = [loc.clone(), proj.clone()].into();
            let typing = Assertion::Types(vec![(loc, Type::ObjectType), (proj, Type::ListType)]);
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
            let proj = GExpr::LVar(self.new_temp());
            let ptr: Expr = [loc.clone(), proj.clone()].into();
            let typing = Assertion::Types(vec![(loc, Type::ObjectType), (proj, Type::ListType)]);
            let non_null = self.make_nonnull(ptr.clone());
            let eq = Formula::Eq {
                left: Box::new(non_null),
                right: Box::new(left),
            };
            let eq = Assertion::Pure(eq);
            let pfs = Assertion::star(typing, eq);
            (ptr, pfs)
        } else if ty_utils::is_mut_ref(left_ty) && self.prophecies_enabled() {
            (left.lnth(0), Assertion::Emp)
        } else {
            (left, Assertion::Emp)
        };
        Assertion::star(pfs, super::core_preds::value(left, ty, right))
    }

    pub fn compile_assertion(&mut self, e: ExprId, thir: &Thir<'tcx>) -> Assertion {
        let expr = &thir.exprs[e];
        if !self.is_assertion_ty(self.subst(expr.ty)) {
            fatal!(self, "{:?} is not the assertion type", self.subst(expr.ty))
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
                Some(LogicStubs::AssertPure) => {
                    assert!(args.len() == 1, "Pure call must have one argument");
                    let formula = self.compile_formula(args[0], thir);
                    Assertion::Pure(formula)
                }
                Some(LogicStubs::AssertObservation) => {
                    assert!(args.len() == 1, "Observation call must have one argment");
                    let formula = self.compile_formula(args[0], thir);
                    super::core_preds::observation(formula)
                }
                Some(LogicStubs::AssertStar) => {
                    assert!(args.len() == 2, "Pure call must have one argument");
                    let left = self.compile_assertion(args[0], thir);
                    let right = self.compile_assertion(args[1], thir);
                    Assertion::star(left, right)
                }
                Some(LogicStubs::AssertEmp) => {
                    assert!(args.len() == 0, "Emp call must have no arguments");
                    Assertion::Emp
                }
                Some(LogicStubs::AssertPointsTo) => self.compile_points_to(args, thir),
                Some(LogicStubs::AssertPointsToSlice) => {
                    self.compile_points_to_slice(args, *ty, thir)
                }
                Some(LogicStubs::AssertUninit) => self.compile_uninit(args, *ty, thir),
                Some(LogicStubs::AssertManyUninits) => self.compile_many_uninits(args, *ty, thir),
                Some(LogicStubs::AssertMaybeUninit) => self.compile_maybe_uninit(args, *ty, thir),
                Some(LogicStubs::AssertManyMaybeUninits) => {
                    self.compile_many_maybe_uninits(args, *ty, thir)
                }
                Some(LogicStubs::ProphecyObserver) => {
                    self.assert_prophecies_enabled("using prophecy::observer");
                    let prophecy = self.compile_expression(args[0], thir);
                    let typ = self
                        .encode_type(self.unwrap_prophecy_ty(self.subst(thir.exprs[args[0]].ty)));
                    let model = self.compile_expression(args[1], thir);
                    super::core_preds::observer(prophecy, typ, model)
                }
                Some(LogicStubs::ProphecyController) => {
                    self.assert_prophecies_enabled("using prophecy::controller");
                    let prophecy = self.compile_expression(args[0], thir);
                    let typ = self
                        .encode_type(self.unwrap_prophecy_ty(self.subst(thir.exprs[args[0]].ty)));
                    let model = self.compile_expression(args[1], thir);
                    super::core_preds::controller(prophecy, typ, model)
                }
                _ => {
                    let (def_id, substs) = match ty.kind() {
                        TyKind::FnDef(def_id, substs) => (*def_id, substs),
                        _ => fatal!(self, "Unsupported Thir expression: {:?}", expr),
                    };
                    let substs = self.subst(*substs);
                    let (name, substs) = self.global_env_mut().resolve_predicate(def_id, substs);
                    let ty_params = param_collector::collect_params_on_args(substs)
                        .with_consider_arguments(args.iter().map(|id| self.subst(thir[*id].ty)));
                    let mut params = Vec::with_capacity(
                        ty_params.parameters.len() + (ty_params.regions as usize) + args.len(),
                    );
                    if ty_params.regions {
                        if !has_generic_lifetimes(self.body_id, self.tcx()) {
                            fatal!(self, "predicate calling another one, it has a lifetime param but not self? in context: {:?}, offender: {ty:?}", self.pred_name())
                        };
                        params.push(Expr::PVar(lifetime_param_name("a")));
                    }
                    for tyarg in ty_params.parameters {
                        let tyarg = self.encode_type(tyarg);
                        params.push(tyarg.into());
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

    pub fn resolve_block(&self, e: ExprId, thir: &Thir<'tcx>) -> Option<BlockId> {
        let expr = &thir.exprs[e];
        match &expr.kind {
            ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.resolve_block(*value, thir),
            ExprKind::Use { source } => self.resolve_block(*source, thir),
            ExprKind::Block { block, .. } => Some(*block),
            _ => None,
        }
    }

    fn peel_scope(&self, mut e: ExprId, thir: &Thir<'tcx>) -> ExprId {
        while let ExprKind::Scope { value, .. } = &thir[e].kind {
            e = *value;
        }
        e
    }

    /// Removes any bindings for lvars surrounding an assertion and adds them to the environment.
    fn peel_lvar_bindings<A>(
        &mut self,
        mut e: ExprId,
        thir: &Thir<'tcx>,
        mut k: impl FnMut(&mut Self, ExprId, &Thir<'tcx>) -> A,
    ) -> A {
        e = self.peel_scope(e, thir);

        match &thir[e].kind {
            ExprKind::Call { ty, args, .. }
                if self.get_stub(*ty) == Some(LogicStubs::InstantiateLVars) =>
            {
                let ExprKind::Closure(clos) = &thir[self.peel_scope(args[0], thir)].kind else {
                    unreachable!()
                };

                let (thir, expr) = get_thir!(self, clos.closure_id.to_def_id());

                for (nm, ty) in fn_args_and_tys(self.tcx(), clos.closure_id.to_def_id()) {
                    self.lvars.insert(nm, ty);
                }

                let Some(block) = self.resolve_block(expr, &*thir) else {
                    unreachable!("closure must start with block")
                };

                assert_eq!(thir[block].stmts.len(), 0);

                k(self, thir[block].expr.unwrap(), &*thir)
            }
            ExprKind::Block { block } => {
                let block = &thir[*block];
                assert!(block.stmts.is_empty());

                // let StmtKind::Expr { expr, .. }  = thir[block.stmts[0]].kind else { panic!() };
                self.peel_lvar_bindings(block.expr.unwrap(), thir, k)
            }
            _ => k(self, e, thir),
        }
    }

    fn compile_assertion_outer(&mut self, e: ExprId, thir: &Thir<'tcx>) -> Assertion {
        let inner =
            self.peel_lvar_bindings(e, thir, |this, e, thir| this.compile_assertion(e, thir));
        
        let inner = std::mem::take(&mut self.local_toplevel_asrts)
            .into_iter()
            .fold(inner, Assertion::star);

        if (!crate::logic::is_function_specification(self.body_id, self.tcx()))
            || (!has_generic_lifetimes(self.body_id, self.tcx()))
        {
            inner
        } else {
            let lft_param = lifetime_param_name("a");
            Assertion::star(
                inner,
                super::core_preds::alive_lft(Expr::LVar(format!("#{lft_param}"))),
            )
        }
    }

    pub(crate) fn resolve(e: ExprId, thir: &Thir<'tcx>) -> ExprId {
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

    pub(crate) fn resolve_array(&self, e: ExprId, thir: &Thir<'tcx>) -> Vec<ExprId> {
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

    pub(crate) fn resolve_definitions(&self, e: ExprId, thir: &Thir<'tcx>) -> Vec<ExprId> {
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
            ExprKind::Call { ty, args, .. } if self.get_stub(*ty) == Some(LogicStubs::PredDefs) => {
                assert!(args.len() == 1, "Defs call must have one argument");
                self.resolve_array(args[0], thir)
            }
            _ => fatal!(self, "Can't resolve definition: {:?}", expr),
        }
    }

    fn compile_formula_closure(mut self) -> Formula {
        let (thir, ret_expr) = get_thir!(self, self.body_id);
        let block = &thir[self.resolve_block(ret_expr, &thir).unwrap()];
        if !block.stmts.is_empty() || block.expr.is_none() {
            fatal!(self, "formula closure is malformed")
        }

        self.compile_formula(block.expr.unwrap(), &thir)
    }

    pub fn compile_abstract(mut self) -> Pred {
        let sig = self.sig();
        self.global_env_mut()
            .mark_pred_as_compiled(sig.name.clone());
        let params: Vec<_> = sig.params();
        Pred {
            name: sig.name,
            num_params: params.len(),
            params,
            abstract_: true,
            facts: sig.facts,
            definitions: vec![],
            ins: sig.ins,
            pure: false,
            guard: sig.guard,
        }
    }

    pub fn compile_concrete(mut self) -> Pred {
        let sig = self.sig();
        let (thir, ret_expr) = get_thir!(self, self.body_id);

        let real_sig = build_signature(self.global_env, self.body_id);
        // FIXME: Use the list of statements of the main block expr
        let raw_definitions: Vec<_> = self
            .resolve_definitions(ret_expr, &thir)
            .iter()
            .map(|e| self.compile_assertion_outer(*e, &thir))
            .collect();
        self.global_env_mut()
            .mark_pred_as_compiled(sig.name.clone());
        let params: Vec<_> = sig.params();

        let mut definitions = Vec::new();

        for d in raw_definitions {
            let mut definition = d;
            definition = real_sig
                .type_wf_pres(self.global_env, self.temp_gen)
                .into_iter()
                .fold(definition, Assertion::star);

            definition = real_sig
                .store_eq_var()
                .into_iter()
                .rfold(definition, Assertion::star);
            definitions.push(definition);
        }

        Pred {
            name: sig.name,
            num_params: params.len(),
            params,
            abstract_: false,
            facts: sig.facts,
            definitions,
            ins: sig.ins,
            pure: false,
            guard: sig.guard,
        }
    }

    pub fn build_var_map(&mut self, thir: &Thir<'tcx>) {
        let arguments = &thir.params;

        for param in arguments {
            let Some(pat) = &param.pat else { continue };
            use rustc_middle::thir::BindingMode;
            match &pat.kind {
                PatKind::Binding {
                    mutability: Mutability::Not,
                    name,
                    mode: BindingMode::ByValue,
                    var,
                    subpattern: None,
                    ..
                } => {
                    self.var_map.insert(*var, GExpr::PVar(name.to_string()));
                }
                _ => {
                    fatal!(self, "unsupported pattern in predicate declaration")
                }
            }
        }
    }

    /// Returns a tuple of universally quantified lvars, precondition, (existentially quantified lvars, postcondition)
    pub fn raw_spec(
        mut self,
    ) -> (
        IndexMap<Symbol, Ty<'tcx>>,
        Assertion,
        (Vec<(Symbol, Ty<'tcx>)>, Assertion),
    ) {
        let (thir, ret_expr) = get_thir!(self, self.body_id);
        self.build_var_map(&thir);

        let (pre_lvars, pre, post) =
            self.peel_lvar_bindings(ret_expr, &*thir, |this, expr, thir| {
                let ExprKind::Call {
                    ty, fun: _, args, ..
                } = &thir[this.peel_scope(expr, thir)].kind
                else {
                    unreachable!("ill formed specification block {:?}", thir[expr])
                };

                let Some(LogicStubs::Spec) = this.get_stub(*ty) else {
                    unreachable!("ill formed specification block")
                };
                // Only keep the lvars from the `instantiate_lvars` for preconditions?
                let pre_lvars = std::mem::take(&mut this.lvars);

                let pre = this.compile_assertion(args[0], thir);

                // assert!(this.local_toplevel_asrts.is_empty(), "TODO(xavier): temporary hack {:?}", this.local_toplevel_asrts);
                // This assertion fails, but probably shoudlnt...

                let _ = std::mem::take(&mut this.local_toplevel_asrts);
                let _ = std::mem::take(&mut this.lvars);

                let mut post = this.peel_lvar_bindings(args[1], thir, |this, expr, thir| {
                    this.compile_assertion(expr, thir)
                });

                post = std::mem::take(&mut this.local_toplevel_asrts)
                    .into_iter()
                    .fold(post, Assertion::star);

                (pre_lvars, pre, post)
            });

        let post_lvars: Vec<_> = self.lvars.into_iter().collect();

        (pre_lvars, pre, (post_lvars, post))
    }
}

fn fn_args_and_tys<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<(Symbol, Ty<'tcx>)> {
    use rustc_hir::def::DefKind;
    use rustc_hir::Unsafety;

    let tys = match tcx.def_kind(def_id) {
        DefKind::Fn | DefKind::AssocFn => tcx
            .fn_sig(def_id)
            .instantiate_identity()
            .inputs()
            .skip_binder(),
        DefKind::Closure => {
            let TyKind::Closure(_, subst) = tcx.type_of(def_id).skip_binder().kind() else {
                unreachable!()
            };
            let closure_args = subst.as_closure().sig();
            tcx.signature_unclosure(closure_args, Unsafety::Normal)
                .inputs()
                .skip_binder()
        }
        k => unreachable!("{k:?}"),
    };
    tcx.fn_arg_names(def_id)
        .iter()
        .zip(tys)
        .map(|(nm, ty)| (nm.name, *ty))
        .collect()
}
