use std::collections::HashMap;

use super::gilsonite::{self, Assert, SpecTerm};
use super::utils::get_thir;
use super::{builtins::LogicStubs, is_borrow};
use crate::logic::gilsonite::SeqOp;
use crate::signature::{build_signature, raw_ins, Signature};
use crate::{
    codegen::place::{GilPlace, GilProj},
    logic::{core_preds, param_collector},
    prelude::*,
    temp_gen::TempGenerator,
    utils::polymorphism::{generic_types, has_generic_lifetimes},
};
use gillian::gil::{Assertion, Expr as GExpr, Pred, Type};
use indexmap::IndexMap;

use rustc_middle::ty::ParamEnv;
use rustc_middle::{
    thir::{LocalVarId, PatKind, Thir},
    ty::{AdtKind, EarlyBinder},
};
use rustc_type_ir::fold::TypeFoldable;

/// Vestigial signature type
pub(crate) struct PredSig {
    name: String,
}

pub(crate) struct PredCtx<'tcx, 'genv> {
    param_env: ParamEnv<'tcx>,
    global_env: &'genv mut GlobalEnv<'tcx>,
    temp_gen: &'genv mut TempGenerator,
    /// Identifier of the item providing the body (aka specification).
    body_id: DefId,
    args: GenericArgsRef<'tcx>,
    var_map: HashMap<LocalVarId, GExpr>,
    local_toplevel_asrts: Vec<Assertion>, // Assertions that are local to a single definition
    lvars: IndexMap<Symbol, Ty<'tcx>>,
    sig: Signature<'tcx>,
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

// FIXME: this code isn't very elegant, there should be also a "LocalLogCtx" with a reference to the thir body,
//        that would allow to not resolve everything every time. Also, it would be reused for other logic items.
impl<'tcx: 'genv, 'genv> PredCtx<'tcx, 'genv> {
    pub(crate) fn new(
        global_env: &'genv mut GlobalEnv<'tcx>,
        temp_gen: &'genv mut TempGenerator,
        // The outermost scope within which this predicate is used.
        // This determines what hte paramenv that we will use during trait resolution is.
        // caller_id: DefId,
        param_env: ParamEnv<'tcx>,
        body_id: DefId,
        args: GenericArgsRef<'tcx>,
    ) -> Self {
        PredCtx {
            sig: build_signature(global_env, body_id, args),
            temp_gen,
            global_env,
            body_id,
            args,
            param_env,
            var_map: HashMap::new(),
            local_toplevel_asrts: Vec::new(),
            lvars: Default::default(),
        }
    }

    pub(crate) fn new_with_identity_args(
        global_env: &'genv mut GlobalEnv<'tcx>,
        temp_gen: &'genv mut TempGenerator,
        body_id: DefId,
    ) -> Self {
        let args = GenericArgs::identity_for_item(global_env.tcx(), body_id);
        let param_env = global_env.tcx().param_env(body_id);
        Self::new(global_env, temp_gen, param_env, body_id, args)
    }

    fn prophecies_enabled(&self) -> bool {
        self.global_env.config.prophecies
    }

    fn subst<F: TypeFoldable<TyCtxt<'tcx>>>(&self, foldable: F) -> F {
        EarlyBinder::bind(foldable).instantiate(self.tcx(), self.args)
    }

    fn encode_type_with_args(&mut self, ty: Ty<'tcx>) -> EncodedType {
        self.encode_type(ty)
    }

    fn assert_prophecies_enabled(&self, msg: &str) {
        if !self.prophecies_enabled() {
            let msg = format!("Prophecies are not enabled: {}", msg);
            self.tcx().dcx().fatal(msg);
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

        if let Some(LogicStubs::OwnPred | LogicStubs::RefMutInner) =
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
                .dcx()
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

    fn pred_name(&self) -> String {
        self.global_env
            .just_pred_name_with_args(self.body_id, self.args)
    }

    fn guard(&self) -> Option<Assertion> {
        is_borrow(self.body_id, self.tcx()).then(|| {
            if !has_generic_lifetimes(self.body_id, self.tcx()) {
                fatal!(self, "Borrow without a lifetime? {:?}", self.pred_name());
            }
            let lft = self.sig.lifetimes().next().unwrap();
            core_preds::alive_lft(Expr::PVar(lft.to_string()))
        })
    }

    fn sig(&mut self) -> PredSig {
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

        // let guard = self.guard();

        PredSig {
            name: self.pred_name(),
            // guard,
        }
    }

    fn unwrap_prophecy_ty(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        match ty.kind() {
            TyKind::Adt(_, args) => args[0].expect_ty(),
            _ => fatal!(self, "Prophecy field on non-prophecy"),
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

    fn compile_many_uninits(
        &mut self,
        pointer: gilsonite::Expr<'tcx>,
        size: gilsonite::Expr<'tcx>,
    ) -> Assertion {
        let ty = pointer.ty.builtin_deref(true).unwrap().ty;
        let pointer = self.compile_expression_inner(pointer);
        let size = self.compile_expression_inner(size);
        let typ = self.encode_type_with_args(ty);

        super::core_preds::many_uninits(pointer, typ, size)
    }

    fn compile_many_maybe_uninits(
        &mut self,
        pointer: gilsonite::Expr<'tcx>,
        size: gilsonite::Expr<'tcx>,
        pointee: gilsonite::Expr<'tcx>,
    ) -> Assertion {
        let ty = pointer.ty.builtin_deref(true).unwrap().ty;

        let pointer = self.compile_expression_inner(pointer);
        let size = self.compile_expression_inner(size);
        let pointee = self.compile_expression_inner(pointee);
        let typ = self.encode_type_with_args(ty);
        super::core_preds::many_maybe_uninits(pointer, typ, size, pointee)
    }

    fn compile_maybe_uninit(
        &mut self,
        pointer: gilsonite::Expr<'tcx>,
        pointee: gilsonite::Expr<'tcx>,
    ) -> Assertion {
        let ty = pointer.ty.builtin_deref(true).unwrap().ty;

        let ty = self.encode_type_with_args(ty);
        let pointer = self.compile_expression_inner(pointer);
        let pointee = self.compile_expression_inner(pointee);

        super::core_preds::maybe_uninit(pointer, ty, pointee)
    }

    fn compile_points_to(
        &mut self,
        src: gilsonite::Expr<'tcx>,
        tgt: gilsonite::Expr<'tcx>,
    ) -> Assertion {
        let ty = self.encode_type_with_args(tgt.ty);
        let left_ty = src.ty;
        let left = self.compile_expression_inner(src);
        let right = self.compile_expression_inner(tgt);
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

    fn compile_assertion(&mut self, assert: Assert<'tcx>) -> Assertion {
        assert!(self.local_toplevel_asrts.is_empty());
        let assert = self.subst(assert);

        let mut assert = self.compile_assertion_inner(assert);
        assert = std::mem::take(&mut self.local_toplevel_asrts)
            .into_iter()
            .fold(assert, Assertion::star);
        assert
    }

    fn compile_assertion_inner(&mut self, gil: gilsonite::Assert<'tcx>) -> Assertion {
        use gilsonite::AssertKind;
        match gil.kind {
            AssertKind::Star { left, right } => self
                .compile_assertion_inner(*left)
                .star(self.compile_assertion_inner(*right)),
            AssertKind::Formula { formula } => Assertion::Pure(self.compile_formula_inner(formula)),
            AssertKind::Call {
                def_id,
                substs,
                args,
            } => {
                let param_env = self.param_env;
                let (name, def_id, substs) = self
                    .global_env_mut()
                    .resolve_predicate_param_env(param_env, def_id, substs);

                let ty_params = param_collector::collect_params_on_args(substs)
                    .with_consider_arguments(args.iter().map(|id| id.ty));
                let mut params = Vec::new();
                let has_regions = build_signature(self.global_env, def_id, substs)
                    .lifetimes()
                    .count()
                    > 0;

                if has_regions {
                    if self.sig.lifetimes().next().is_none() {
                        fatal!(
                            self,
                            "predicate calling ({:?}) another one ({:?}), it has a lifetime param but not self?", self.body_id, def_id
                        )
                    };
                    let lft = self.sig.lifetimes().next().unwrap();

                    params.push(Expr::PVar(lft.to_string()));
                }
                for tyarg in ty_params.parameters {
                    let tyarg = self.encode_param_ty(tyarg);
                    params.push(tyarg.into());
                }
                for arg in args.into_iter() {
                    params.push(self.compile_expression_inner(arg));
                }
                Assertion::Pred { name, params }
            }
            AssertKind::PointsTo { src, tgt } => self.compile_points_to(src, tgt),
            AssertKind::Emp => Assertion::Emp,
            AssertKind::Observation { formula } => {
                let formula = self.compile_formula_inner(formula);
                core_preds::observation(formula)
            }
            AssertKind::ProphecyController { prophecy, model } => {
                self.assert_prophecies_enabled("using prophecy::controller");
                let prophecy = self.compile_expression_inner(prophecy);
                let model = self.compile_expression_inner(model);
                super::core_preds::controller(prophecy, model)
            }
            AssertKind::ProphecyObserver { prophecy, model } => {
                self.assert_prophecies_enabled("using prophecy::controller");
                let prophecy = self.compile_expression_inner(prophecy);
                let model = self.compile_expression_inner(model);
                super::core_preds::observer(prophecy, model)
            }
            AssertKind::PointsToSlice {
                src,
                size,
                pointees,
            } => {
                let ty = src.ty.builtin_deref(true).unwrap().ty;
                let pointer = self.compile_expression_inner(src);
                let size = self.compile_expression_inner(size);
                let pointees = self.compile_expression_inner(pointees);

                let typ = self.encode_array_type(ty, size);
                super::core_preds::value(pointer, typ, pointees)
            }
            AssertKind::Uninit { pointer } => {
                let ty = pointer.ty.builtin_deref(true).unwrap().ty;
                let pointer = self.compile_expression_inner(pointer);
                let typ = self.encode_type_with_args(ty);

                super::core_preds::uninit(pointer, typ)
            }
            AssertKind::ManyUninits { pointer, size } => self.compile_many_uninits(pointer, size),
            AssertKind::MaybeUninit { pointer, pointee } => {
                self.compile_maybe_uninit(pointer, pointee)
            }
            AssertKind::ManyMaybeUninits {
                pointer,
                pointees,
                size,
            } => self.compile_many_maybe_uninits(pointer, size, pointees),
        }
    }

    pub(crate) fn compile_abstract(mut self) -> Pred {
        let sig = self.sig();
        self.global_env_mut()
            .mark_pred_as_compiled(sig.name.clone());
        let params: Vec<_> = self
            .sig
            .args
            .iter()
            .map(|a| (a.name().to_string(), None))
            .collect();
        let mut ins = raw_ins(self.tcx(), self.body_id);
        let num_generics = self.sig.type_params().chain(self.sig.lifetimes()).count();
        ins = (0..num_generics)
            .chain(ins.into_iter().map(|i| i + num_generics))
            .collect();

        Pred {
            name: sig.name,
            num_params: params.len(),
            params,
            abstract_: true,
            facts: vec![],
            definitions: vec![],
            ins,
            pure: false,
            guard: self.guard(),
        }
    }

    pub(crate) fn compile_concrete(mut self) -> Pred {
        let sig = self.sig();
        let name = sig.name.clone();

        let real_sig = build_signature(self.global_env, self.body_id, self.args);
        let raw_definitions = self.global_env.predicate(self.body_id).clone().disjuncts;

        let raw_definitions: Vec<_> = raw_definitions
            .into_iter()
            .map(|a| self.compile_assertion(a.1))
            .collect();

        self.global_env_mut().mark_pred_as_compiled(name);
        let params: Vec<_> = self
            .sig
            .args
            .iter()
            .map(|a| (a.name().to_string(), None))
            .collect();

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

        let mut ins = raw_ins(self.tcx(), self.body_id);
        let num_generics = self.sig.type_params().chain(self.sig.lifetimes()).count();
        ins = (0..num_generics)
            .chain(ins.into_iter().map(|i| i + num_generics))
            .collect();

        Pred {
            name: sig.name,
            num_params: params.len(),
            params,
            abstract_: false,
            facts: vec![],
            definitions,
            ins,
            pure: false,
            guard: self.guard(),
        }
    }

    fn build_var_map(&mut self, thir: &Thir<'tcx>) {
        let arguments = &thir.params;

        for param in arguments {
            let Some(pat) = &param.pat else { continue };
            use rustc_ast::ast::BindingMode;
            match &pat.kind {
                PatKind::Binding {
                    // mutability: Mutability::Not,
                    name,
                    mode: BindingMode::NONE,
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
    pub(crate) fn raw_spec(
        mut self,
    ) -> (
        IndexMap<Symbol, Ty<'tcx>>,
        Assertion,
        (Vec<(Symbol, Ty<'tcx>)>, Assertion),
    ) {
        let (thir, _) = get_thir!(self, self.body_id);
        self.build_var_map(&thir);

        let SpecTerm {
            uni,
            pre,
            exi,
            post,
        } = self.global_env.gilsonite_spec(self.body_id).clone();

        let pre = self.compile_assertion(pre);
        let post = self.compile_assertion(post);

        (uni.into_iter().collect(), pre, (exi, post))
        // (uni.into_iter().collect(), pre, (exi, post))
    }

    fn compile_formula_inner(&mut self, formula: gilsonite::Formula<'tcx>) -> Formula {
        assert!(formula.bound_vars.is_empty());

        self.compile_formula_body(formula.body)
    }

    fn compile_formula_body(&mut self, formula: gilsonite::FormulaKind<'tcx>) -> Formula {
        use gilsonite::{EOp, FOp, FormulaKind};
        match formula {
            // FormulaKind::True => Formula::True,
            // FormulaKind::False => Formula::False,
            FormulaKind::FOp { left, op, right } => {
                let left = self.compile_formula_body(*left);
                let right = self.compile_formula_body(*right);
                match op {
                    FOp::Impl => left.implies(right),
                    FOp::Or => left.or(right),
                    FOp::And => left.and(right),
                }
            }
            FormulaKind::EOp { left, op, right } => {
                let ty = left.ty;
                let left = Box::new(self.compile_expression_inner(*left));
                let right = Box::new(self.compile_expression_inner(*right));
                match op {
                    EOp::Lt => {
                        if ty.is_floating_point() {
                            Formula::FLess { left, right }
                        } else {
                            Formula::ILess { left, right }
                        }
                    }
                    // TODO: Handle string case too (requires knowing what types its defined on)
                    EOp::Le => {
                        if ty.is_floating_point() {
                            Formula::FLessEq { left, right }
                        } else {
                            Formula::ILessEq { left, right }
                        }
                    }
                    EOp::Eq => left.eq_f(*right),
                    EOp::SetMem => Formula::SetMem { left, right },
                    EOp::SetSub => Formula::SetSub { left, right },
                    EOp::Ne => left.eq_f(*right).fnot(),
                }
            }
            FormulaKind::Neg { form } => self.compile_formula_body(*form).fnot(),
        }
    }

    fn compile_expression_inner(&mut self, body: gilsonite::Expr<'tcx>) -> GExpr {
        use gilsonite::{BinOp, ExprKind};
        match body.kind {
            ExprKind::Call {
                def_id,
                substs,
                args,
            } => {
                let mut params: Vec<_> = substs
                    .iter()
                    .filter_map(|x| self.encode_generic_arg(x))
                    .map(|x| x.into())
                    .collect();
                params.extend(args.into_iter().map(|e| self.compile_expression_inner(e)));

                let fn_sig = self.tcx().fn_sig(def_id).skip_binder();
                let out = fn_sig.output().skip_binder();
                let out_var = self.temp_lvar(out);
                params.push(out_var.clone());

                let pred_call = Assertion::Pred {
                    name: self.tcx().def_path_str(def_id),
                    params,
                };

                self.local_toplevel_asrts.push(pred_call);
                out_var
            }
            ExprKind::BinOp { left, op, right } => {
                let left_ty = left.ty;
                let left = self.compile_expression_inner(*left);
                let right = self.compile_expression_inner(*right);
                match op {
                    BinOp::Eq => GExpr::eq_expr(left, right),
                    BinOp::Lt => todo!(),
                    BinOp::Le => todo!(),
                    BinOp::Ne => todo!(),
                    BinOp::Sub => {
                        if left_ty.is_integral() {
                            GExpr::minus(left, right)
                        } else {
                            GExpr::fminus(left, right)
                        }
                    }
                    BinOp::Add => {
                        if left_ty.is_integral() {
                            GExpr::plus(left, right)
                        } else {
                            GExpr::fplus(left, right)
                        }
                    }
                    BinOp::Shl => {
                        if left_ty.is_integral() {
                            GExpr::i_shl(left, right)
                        } else {
                            todo!("shl for floats")
                        }
                    }
                }
            }
            ExprKind::Constructor {
                def_id,
                _args: _,
                fields,
                variant_index,
            } => {
                let fields: Vec<_> = fields
                    .into_iter()
                    .map(|f| self.compile_expression_inner(f))
                    .collect();

                match self.tcx().adt_def(def_id).adt_kind() {
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
            ExprKind::Tuple { fields } => {
                let fields: Vec<_> = fields
                    .into_iter()
                    .map(|f| self.compile_expression_inner(f))
                    .collect();
                fields.into()
            }
            ExprKind::Field { lhs, field } => {
                if matches!(lhs.ty.kind(), TyKind::Tuple(..)) {
                    self.compile_expression_inner(*lhs).lnth(field.as_u32())
                } else if lhs.ty.is_any_ptr() {
                    let ty = lhs.ty.builtin_deref(true).unwrap().ty;
                    let gil_derefed = self.compile_expression_inner(*lhs);
                    let mut place = GilPlace::base(gil_derefed, ty);
                    if ty.is_enum() {
                        panic!("enum field, need to handle")
                    }
                    place.proj.push(GilProj::Field(
                        field.as_u32(),
                        self.encode_type_with_args(ty),
                    ));
                    if self.prophecies_enabled() {
                        [place.into_expr_ptr(), [Expr::null(), vec![].into()].into()].into()
                    } else {
                        place.into_expr_ptr()
                    }
                } else {
                    match lhs.ty.ty_adt_def() {
                        Some(adt) => {
                            if adt.is_struct() {
                                let lhs = self.compile_expression_inner(*lhs);
                                lhs.lnth(field.as_usize())
                            } else {
                                fatal!(self, "Can't use field access on enums in assertions.")
                            }
                        }
                        None => fatal!(self, "Field access on non-adt in assertion? {:?}", lhs.ty),
                    }
                }
            }
            // It seems like *every* variable appearing in a contract should be made an lvar except for ret
            ExprKind::Var { id } => {
                if id.as_str() == "ret" {
                    GExpr::PVar(format!("{id}"))
                } else {
                    GExpr::LVar(format!("#{id}"))
                }
            }

            ExprKind::Integer { value } => value.into(),
            ExprKind::SeqNil => GExpr::EList(vec![]),
            ExprKind::SeqOp { op, args } => {
                let mut args: Vec<_> = args
                    .into_iter()
                    .map(|a| self.compile_expression_inner(a))
                    .collect();
                match op {
                    SeqOp::Append => args.remove(0).lst_concat(vec![args.remove(0)].into()),
                    SeqOp::Prepend => {
                        GExpr::lst_concat(vec![args.remove(1)].into(), args.remove(0))
                    }
                    SeqOp::Concat => args.remove(0).lst_concat(args.remove(0)),
                    SeqOp::Head => args.remove(0).lst_head(),
                    SeqOp::Tail => args.remove(0).lst_tail(),
                    SeqOp::Len => args.remove(0).lst_len(),

                    SeqOp::At => args.remove(0).lnth_e(args.remove(0)),
                    SeqOp::Sub => args.remove(0).lst_sub_e(args.remove(0), args.remove(0)),
                    SeqOp::Repeat => args.remove(0).repeat(args.remove(0)),
                }
            }
            ExprKind::ZST => vec![].into(),
            ExprKind::SetProphecy { mut_ref, prophecy } => {
                self.assert_prophecies_enabled("using `Prophecised::assign`");
                let mut_ref = self.compile_expression_inner(*mut_ref);
                let pcy = self.compile_expression_inner(*prophecy);
                [mut_ref.lnth(0), pcy].into()
            }
            ExprKind::GetProphecy { mut_ref } => {
                self.assert_prophecies_enabled("using `Prophecised::prophecy`");
                let mut_ref = self.compile_expression_inner(*mut_ref);
                mut_ref.lnth(1)
            }
            ExprKind::GetValue { mut_ref } => {
                self.assert_prophecies_enabled("using `Prophecy::value`");
                let ty = self
                    .tcx()
                    .try_normalize_erasing_regions(self.param_env, mut_ref.ty)
                    .unwrap_or(mut_ref.ty);
                let ty = self.unwrap_prophecy_ty(ty);
                let prophecy = self.compile_expression_inner(*mut_ref);
                let value = self.temp_lvar(ty);
                self.local_toplevel_asrts
                    .push(core_preds::pcy_value(prophecy, value.clone()));
                value
            }
        }
    }
}

pub fn fn_args_and_tys(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<(Symbol, Ty<'_>)> {
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
