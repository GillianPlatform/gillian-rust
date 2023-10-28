use std::collections::HashMap;

use super::builtins::LogicStubs;
use super::utils::get_thir;
use crate::{
    codegen::{
        place::{GilPlace, GilProj},
        typ_encoding::{lifetime_param_name, type_param_name},
    },
    logic::{core_preds, param_collector},
    prelude::*,
    temp_gen::TempGenerator,
    utils::polymorphism::HasGenericArguments,
};
use gillian::gil::{Assertion, Expr as GExpr, Pred, Type};
use rustc_ast::{AttrArgs, AttrArgsEq, LitKind, MetaItemLit, StrStyle};

use rustc_middle::{
    mir::{interpret::Scalar, BinOp, BorrowKind},
    thir::{AdtExpr, BlockId, ExprId, ExprKind, LocalVarId, Param, Pat, PatKind, StmtKind, Thir},
    ty::{AdtKind, EarlyBinder},
};
use rustc_target::abi::FieldIdx;
use rustc_type_ir::fold::TypeFoldable;

pub(crate) struct PredSig {
    pub name: String,
    pub params: Vec<(String, Option<Type>)>,
    pub ins: Vec<usize>,
    pub facts: Vec<Formula>,
    pub guard: Option<Assertion>,
}

pub(crate) struct PredCtx<'tcx, 'genv> {
    pub global_env: &'genv mut GlobalEnv<'tcx>,
    pub temp_gen: &'genv mut TempGenerator,
    pub did: DefId,
    pub args: GenericArgsRef<'tcx>,
    pub var_map: HashMap<LocalVarId, GExpr>,
    pub local_toplevel_asrts: Vec<Assertion>, // Assertions that are local to a single definition
    pub global_toplevel_asrts: Vec<Assertion>, // Assertion that are global to all definitions
}

impl<'tcx> HasGenericArguments<'tcx> for PredCtx<'tcx, '_> {}

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

impl HasDefId for PredCtx<'_, '_> {
    fn did(&self) -> DefId {
        self.did
    }
}

// FIXME: this code isn't very elegant, there should be also a "LocalLogCtx" with a reference to the thir body,
//        that would allow to not resolve everything every time. Also, it would be reused for other logic items.
impl<'tcx: 'genv, 'genv> PredCtx<'tcx, 'genv> {
    pub fn new(
        global_env: &'genv mut GlobalEnv<'tcx>,
        temp_gen: &'genv mut TempGenerator,
        did: DefId,
        args: GenericArgsRef<'tcx>,
    ) -> Self {
        PredCtx {
            temp_gen,
            global_env,
            did,
            args,
            var_map: HashMap::new(),
            local_toplevel_asrts: Vec::new(),
            global_toplevel_asrts: Vec::new(),
        }
    }

    pub fn new_with_identity_args(
        global_env: &'genv mut GlobalEnv<'tcx>,
        temp_gen: &'genv mut TempGenerator,
        did: DefId,
    ) -> Self {
        let args = GenericArgs::identity_for_item(global_env.tcx(), did);
        Self::new(global_env, temp_gen, did, args)
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

    fn temp_lvar(&mut self) -> GExpr {
        Expr::LVar(self.new_temp())
    }

    fn get_ins(&self) -> Vec<usize> {
        // Special case for items that are in gilogic.
        // This code yeets as soon as we can do multi-crate.

        if let Some(LogicStubs::OwnPred | LogicStubs::RefMutInner | LogicStubs::OptionOwnPred) =
            LogicStubs::of_def_id(self.did(), self.tcx())
        {
            return vec![0];
        }

        let Some(ins_attr) = crate::utils::attrs::get_attr(
            self.tcx().get_attrs_unchecked(self.did),
            &["gillian", "decl", "pred_ins"],
        ) else {
            fatal!(
                self,
                "Predicate {:?} doesn't have ins attribute",
                self.pred_name()
            )
        };

        let str_arg = if let AttrArgs::Eq(
            _,
            AttrArgsEq::Hir(MetaItemLit {
                kind: LitKind::Str(sym, StrStyle::Cooked),
                ..
            }),
        ) = ins_attr.args
        {
            sym.as_str().to_owned()
        } else {
            self.tcx()
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

    pub fn pred_name(&self) -> String {
        self.global_env
            .just_pred_name_with_args(self.did, self.args)
    }

    fn make_is_ptr_asrt(&mut self, e: GExpr) -> Assertion {
        let loc = self.temp_lvar();
        let proj = self.temp_lvar();
        let types = Assertion::Types(vec![
            (loc.clone(), Type::ObjectType),
            (proj.clone(), Type::ListType),
        ]);
        types.star(e.eq_f([loc, proj]).into_asrt())
    }

    fn make_is_nonnull_asrt(&mut self, e: GExpr) -> Assertion {
        let loc = self.temp_lvar();
        let proj = self.temp_lvar();
        let types = Assertion::Types(vec![
            (loc.clone(), Type::ObjectType),
            (proj.clone(), Type::ListType),
        ]);
        types.star(e.eq_f([Expr::EList(vec![loc, proj])]).into_asrt())
    }

    fn make_is_unique_asrt(&mut self, e: GExpr) -> Assertion {
        let loc = self.temp_lvar();
        let proj = self.temp_lvar();
        let types = Assertion::Types(vec![
            (loc.clone(), Type::ObjectType),
            (proj.clone(), Type::ListType),
        ]);
        types.star(
            e.eq_f([
                Expr::EList(vec![Expr::EList(vec![loc, proj])]),
                vec![].into(),
            ])
            .into_asrt(),
        )
    }

    fn make_is_mut_ref_proph_ref_asrt(&mut self, e: GExpr) -> Assertion {
        let loc = self.temp_lvar();
        let proj = self.temp_lvar();
        let pcy = self.temp_lvar();
        let pcy_proj = Expr::from(vec![]);
        let types = Assertion::Types(vec![
            (loc.clone(), Type::ObjectType),
            (proj.clone(), Type::ListType),
            (pcy_proj.clone(), Type::ListType),
        ]);
        types.star(e.eq_f([[loc, proj], [pcy, pcy_proj]]).into_asrt())
    }

    fn make_wf_asrt(&mut self, e: GExpr, ty: Ty<'tcx>) -> Assertion {
        // The type here is already substituted
        if ty.is_any_ptr() {
            if ty_utils::is_mut_ref(ty) && self.prophecies_enabled() {
                self.make_is_mut_ref_proph_ref_asrt(e)
            } else {
                self.make_is_ptr_asrt(e)
            }
        } else if ty.is_integral() {
            Assertion::Types(vec![(e, Type::IntType)])
        } else if self.is_nonnull(ty) {
            self.make_is_nonnull_asrt(e)
        } else if self.is_unique(ty) {
            self.make_is_unique_asrt(e)
        } else {
            Assertion::Emp
        }
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
                let ty = self.subst(param.ty);
                if !is_primary {
                    fatal!(self, "Predicate parameters must be primary");
                }
                if subpattern.is_some() {
                    fatal!(self, "Predicate parameters cannot have subpatterns");
                }
                let lvar = GExpr::LVar(format!("#{name}"));

                self.var_map.insert(*var, lvar.clone());
                // Global toplevel asrts that are pure should prob be added to the facts instead of here.
                self.global_toplevel_asrts
                    .push(GExpr::PVar(name.clone()).eq_f(lvar.clone()).into_asrt()); // All pvars are used through their lvars, and something of the form `(p == #p)`
                let type_knowledge = self.make_wf_asrt(lvar, ty);
                self.global_toplevel_asrts.push(type_knowledge);
                (name, ty)
            }
            _ => fatal!(self, "Predicate parameters must be variables"),
        }
    }

    fn guard(&self) -> Option<Assertion> {
        crate::utils::attrs::get_attr(
            self.tcx().get_attrs_unchecked(self.did()),
            &["gillian", "borrow"],
        )
        .map(|_| {
            if !self.has_generic_lifetimes() {
                fatal!(self, "Borrow without a lifetime? {:?}", self.pred_name());
            }
            core_preds::alive_lft(Expr::PVar(lifetime_param_name("a")))
        })
    }

    pub fn sig(&mut self) -> PredSig {
        let has_generic_lifetimes = self.has_generic_lifetimes();
        let generic_types = self.generic_types();
        let mut ins = self.get_ins();
        let generics_amount = generic_types.len() + (has_generic_lifetimes as usize);
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
        let generic_lft_params = if has_generic_lifetimes {
            Some((lifetime_param_name("a"), None)).into_iter()
        } else {
            None.into_iter()
        };
        let generic_type_params = generic_types
            .into_iter()
            .map(|x| (type_param_name(x.0, x.1), None));
        // There are two caes:
        // - either there is a thir body, in which case we can use "extract_params"
        // - or there is not thir body, in which case we don't have param names and we just create arbitrary names
        //   with the right type
        let thir_body = self
            .did()
            .as_local()
            .and_then(|did| self.tcx().thir_body(did).ok().map(|x| x.0));
        let arguments: Vec<_> = match thir_body {
            Some(thir_body) => thir_body
                .borrow()
                .params
                .iter()
                .map(|p| {
                    let (name, _substed_ty) = self.extract_param(p);
                    (name, None)
                })
                .collect(),
            None => {
                let sig = self.tcx().fn_sig(self.did()).instantiate_identity();
                (0..sig.inputs().skip_binder().len())
                    .map(|i| (format!("param_{}", i), None))
                    .collect()
            }
        };
        let params: Vec<_> = generic_lft_params
            .chain(generic_type_params)
            .chain(arguments)
            .collect();
        let guard = self.guard();
        PredSig {
            name: self.pred_name(),
            params,
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
                            fatal!(self, "Unsupported type for << {:?}", ty);
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
                Some(LogicStubs::SeqLen) => {
                    let list = self.compile_expression(args[0], thir);
                    list.lst_len()
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
                    let ty = self.encode_type(ty);
                    let value = self.temp_lvar();
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

                    let out_var = self.temp_lvar();
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
                self.did()
            ),
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
                        Formula::Eq { left, right }
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
                    Some(LogicStubs::FormulaNeg) => {
                        let inner = Box::new(self.compile_formula(args[0], thir));
                        Formula::Not(inner)
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

    fn is_unique(&self, ty: Ty<'tcx>) -> bool {
        crate::utils::ty::is_unique(ty, self.tcx())
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
                Some(LogicStubs::AssertUninit) => self.compile_uninit(args, *ty, thir),
                Some(LogicStubs::AssertManyUninits) => self.compile_many_uninits(args, *ty, thir),
                Some(LogicStubs::AssertMaybeUninit) => self.compile_maybe_uninit(args, *ty, thir),
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
                        if !self.has_generic_lifetimes() {
                            fatal!(self, "predicate calling another one, it has a lifetime param but not self?? {:?}", self.pred_name())
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

    pub fn resolve_block(&self, e: ExprId, thir: &Thir<'tcx>) -> BlockId {
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

    // Returns the list of pvars, not lvars.
    pub(crate) fn add_block_lvars(&mut self, block: BlockId, thir: &Thir<'tcx>) -> Vec<String> {
        let block = &thir[block];
        let mut res = Vec::with_capacity(block.stmts.len());
        for stmt in block.stmts.iter() {
            // We could do additional check that the rhs is actually a call
            // to `gilogic::new_lvar()` but 🤷‍♂️.
            if let StmtKind::Let {
                pattern:
                    box Pat {
                        kind:
                            PatKind::Binding { name, var, ty, .. }
                            | PatKind::AscribeUserType {
                                ascription: _,
                                subpattern:
                                    box Pat {
                                        kind: PatKind::Binding { name, var, ty, .. },
                                        ..
                                    },
                            },
                        ..
                    },
                ..
            } = thir.stmts[*stmt].kind
            {
                let lvar_expr = GExpr::LVar(format!("#{}", name.as_str()));
                let wf_cond = self.make_wf_asrt(lvar_expr.clone(), ty);
                self.local_toplevel_asrts.push(wf_cond);
                self.var_map.insert(var, lvar_expr);
                res.push(name.to_string());
            } else {
                fatal!(
                    self,
                    "Unsupported statement in assertion: {:?}",
                    thir.stmts[*stmt]
                )
            }
        }
        res
    }

    fn compile_assertion_outer(&mut self, e: ExprId, thir: &Thir<'tcx>) -> Assertion {
        let block = self.resolve_block(e, thir);
        self.add_block_lvars(block, thir);
        let block = &thir.blocks[block];
        let expr = block
            .expr
            .unwrap_or_else(|| fatal!(self, "Assertion block has no expression?"));
        let inner = self.compile_assertion(expr, thir);
        let inner = self
            .global_toplevel_asrts
            .iter()
            .fold(inner, |acc, eq| Assertion::star(acc, eq.clone()));
        let inner = std::mem::take(&mut self.local_toplevel_asrts)
            .into_iter()
            .fold(inner, Assertion::star);

        if (!crate::logic::is_function_specification(self.did(), self.tcx()))
            || (!self.has_generic_lifetimes())
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
            _ => fatal!(self, "Can't resolve array: {:?}", expr),
        }
    }

    pub fn compile_abstract(mut self) -> Pred {
        let PredSig {
            name,
            params,
            ins,
            facts,
            guard,
        } = self.sig();
        self.global_env_mut().mark_pred_as_compiled(name.clone());
        Pred {
            name,
            num_params: params.len(),
            params,
            abstract_: true,
            facts,
            definitions: vec![],
            ins,
            pure: false,
            guard,
        }
    }

    pub fn compile_concrete(mut self) -> Pred {
        let PredSig {
            name,
            params,
            ins,
            facts,
            guard,
        } = self.sig();
        let (thir, ret_expr) = get_thir!(self);
        // FIXME: Use the list of statements of the main block expr
        let definitions = self
            .resolve_definitions(ret_expr, &thir)
            .iter()
            .map(|e| self.compile_assertion_outer(*e, &thir))
            .collect();
        self.global_env_mut().mark_pred_as_compiled(name.clone());

        Pred {
            name,
            num_params: params.len(),
            params,
            abstract_: false,
            facts,
            definitions,
            ins,
            pure: false,
            guard,
        }
    }
}
