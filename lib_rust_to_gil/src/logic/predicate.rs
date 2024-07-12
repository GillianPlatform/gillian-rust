use super::gilsonite::{self, Assert, Pattern, Predicate, SpecTerm};
use super::is_borrow;
use crate::logic::gilsonite::{AssertPredCall, SeqOp};
use crate::signature::{build_signature, raw_ins, Signature};
use crate::{
    codegen::place::{GilPlace, GilProj},
    logic::{core_preds, param_collector},
    prelude::*,
    temp_gen::TempGenerator,
    utils::polymorphism::has_generic_lifetimes,
};
use gillian::gil::{Assertion, Expr as GExpr, Pred, Type};
use indexmap::IndexMap;

use rustc_middle::ty::ParamEnv;
use rustc_middle::ty::{AdtKind, EarlyBinder};
use rustc_type_ir::fold::TypeFoldable;

/// Vestigial signature type
pub(crate) struct PredSig {
    name: String,
}

pub(crate) struct PredCtx<'tcx, 'genv> {
    param_env: ParamEnv<'tcx>,
    global_env: &'genv mut GlobalEnv<'tcx>,
    // Deprecated: Remove this
    body_id: DefId,
    args: GenericArgsRef<'tcx>,
    local_toplevel_asrts: Vec<Assertion>, // Assertions that are local to a single definition
    lvars: IndexMap<Symbol, Ty<'tcx>>,
    sig: Signature<'tcx, 'genv>,
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
            sig: build_signature(global_env, body_id, args, temp_gen),
            global_env,
            body_id,
            args,
            param_env,
            local_toplevel_asrts: Vec::new(),
            lvars: Default::default(),
        }
    }

    pub(crate) fn new_with_args(
        global_env: &'genv mut GlobalEnv<'tcx>,
        temp_gen: &'genv mut TempGenerator,
        body_id: DefId,
        args: GenericArgsRef<'tcx>,
    ) -> Self {
        let param_env = global_env.tcx().param_env(body_id);
        let param_env = EarlyBinder::bind(param_env).instantiate(global_env.tcx(), args);
        Self::new(global_env, temp_gen, param_env, body_id, args)
    }

    pub(crate) fn new_with_identity_args(
        global_env: &'genv mut GlobalEnv<'tcx>,
        temp_gen: &'genv mut TempGenerator,
        body_id: DefId,
    ) -> Self {
        let args = GenericArgs::identity_for_item(global_env.tcx(), body_id);
        Self::new_with_args(global_env, temp_gen, body_id, args)
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
        self.sig.temp_gen.fresh_lvar()
    }

    fn temp_lvar(&mut self, ty: Ty<'tcx>) -> GExpr {
        let name = self.new_temp();

        // HACK(xavier): Fix this later once the `mk_wf_asrt` is removed;
        self.lvars.insert(Symbol::intern(&name), ty);
        Expr::LVar(name)
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
            let lft = self.sig.lifetimes().next().unwrap();
            core_preds::alive_lft(Expr::PVar(lft.to_string()))
        })
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
        let pointer = self.compile_expression(pointer);
        let size = self.compile_expression(size);
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

        let pointer = self.compile_expression(pointer);
        let size = self.compile_expression(size);
        let pointee = self.compile_expression(pointee);
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
        let pointer = self.compile_expression(pointer);
        let pointee = self.compile_expression(pointee);

        super::core_preds::maybe_uninit(pointer, ty, pointee)
    }

    fn compile_points_to(
        &mut self,
        src: gilsonite::Expr<'tcx>,
        tgt: gilsonite::Expr<'tcx>,
    ) -> Assertion {
        let ty = self.encode_type_with_args(tgt.ty);
        let left_ty = src.ty;
        let left = self.compile_expression(src);
        let right = self.compile_expression(tgt);
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

    pub fn compile_assertion(&mut self, assert: Assert<'tcx>) -> Assertion {
        assert!(self.local_toplevel_asrts.is_empty());
        let assert = self.subst(assert);

        let mut assert = self.compile_assertion_inner(assert);
        assert = std::mem::take(&mut self.local_toplevel_asrts)
            .into_iter()
            .fold(assert, Assertion::star);
        assert
    }

    pub fn compile_pred_call(
        &mut self,
        call: gilsonite::AssertPredCall<'tcx>,
    ) -> (String, Vec<Expr>) {
        let AssertPredCall {
            def_id,
            substs,
            args,
        } = call;
        let param_env = self.param_env;
        let (name, def_id, substs) = self
            .global_env_mut()
            .resolve_predicate_param_env(param_env, def_id, substs);

        let ty_params = param_collector::collect_params_on_args(substs)
            .with_consider_arguments(args.iter().map(|id| id.ty));
        let mut params = Vec::new();
        let has_regions = build_signature(self.global_env, def_id, substs, &mut self.sig.temp_gen)
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
            params.push(self.compile_expression(arg));
        }

        (name, params)
    }

    fn compile_assertion_inner(&mut self, gil: gilsonite::Assert<'tcx>) -> Assertion {
        use gilsonite::AssertKind;
        match gil.kind {
            AssertKind::Star { left, right } => self
                .compile_assertion_inner(*left)
                .star(self.compile_assertion_inner(*right)),
            AssertKind::Formula { formula } => Assertion::Pure(self.compile_formula(formula)),
            AssertKind::Call(call) => {
                let (name, params) = self.compile_pred_call(call);
                Assertion::Pred { name, params }
            }
            AssertKind::PointsTo { src, tgt } => self.compile_points_to(src, tgt),
            AssertKind::Emp => Assertion::Emp,
            AssertKind::Observation { expr } => {
                let expr = self.compile_expression(expr);
                core_preds::observation(expr)
            }
            AssertKind::ProphecyController { prophecy, model } => {
                self.assert_prophecies_enabled("using prophecy::controller");
                let prophecy = self.compile_expression(prophecy);
                let model = self.compile_expression(model);
                super::core_preds::controller(prophecy, model)
            }
            AssertKind::ProphecyObserver { prophecy, model } => {
                self.assert_prophecies_enabled("using prophecy::controller");
                let prophecy = self.compile_expression(prophecy);
                let model = self.compile_expression(model);
                super::core_preds::observer(prophecy, model)
            }
            AssertKind::PointsToSlice {
                src,
                size,
                pointees,
            } => {
                let ty = src.ty.builtin_deref(true).unwrap().ty;
                let pointer = self.compile_expression(src);
                let size = self.compile_expression(size);
                let pointees = self.compile_expression(pointees);

                let typ = self.encode_array_type(ty, size);
                super::core_preds::value(pointer, typ, pointees)
            }
            AssertKind::Uninit { pointer } => {
                let ty = pointer.ty.builtin_deref(true).unwrap().ty;
                let pointer = self.compile_expression(pointer);
                let typ = self.encode_type_with_args(ty);

                super::core_preds::uninit(pointer, typ)
            }
            AssertKind::ManyUninits { pointer, size } => self.compile_many_uninits(pointer, size),
            AssertKind::MaybeUninit { pointer, pointee } => {
                self.compile_maybe_uninit(pointer, pointee)
            }
            AssertKind::Let { pattern, arg, body } => {
                let arg = self.compile_expression(arg);
                let body = self.compile_assertion(*body);

                let pat = self.compile_pattern(pattern);

                arg.eq_f(pat).into_asrt().star(body)
            }
            AssertKind::ManyMaybeUninits {
                pointer,
                pointees,
                size,
            } => self.compile_many_maybe_uninits(pointer, size, pointees),
        }
    }

    fn compile_pattern(&mut self, pat: Pattern<'tcx>) -> GExpr {
        match pat {
            Pattern::Constructor {
                adt,
                substs,
                variant,
                fields,
            } => todo!("compiler_pattern: constructor"),
            Pattern::Tuple(pats) => {
                let fields: Vec<_> = pats.into_iter().map(|f| self.compile_pattern(f)).collect();
                fields.into()
            }
            Pattern::Wildcard(ty) => self.temp_lvar(ty),
            Pattern::Binder(s) => Expr::LVar(format!("#{s}")),
            Pattern::Boolean(_) => todo!("compile_pattern: boolean"),
        }
    }

    pub(crate) fn compile_abstract(mut self) -> Pred {
        let name = self.pred_name();
        self.global_env_mut().mark_pred_as_compiled(name.clone());
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
            name: name,
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

    pub(crate) fn compile_predicate_body(&mut self, pred: Predicate<'tcx>) -> Vec<Assertion> {
        let raw_definitions = pred.disjuncts;

        let raw_definitions: Vec<_> = raw_definitions
            .into_iter()
            .map(|a| self.compile_assertion(a.1))
            .collect();

        let mut real_sig =
            build_signature(self.global_env, self.body_id, self.args, self.sig.temp_gen);

        let mut definitions = Vec::new();

        for d in raw_definitions {
            let mut definition = d;
            definition = real_sig
                .type_wf_pres(self.global_env)
                .into_iter()
                .fold(definition, Assertion::star);

            definition = real_sig
                .store_eq_var()
                .into_iter()
                .rfold(definition, Assertion::star);
            definitions.push(definition);
        }
        definitions
    }

    pub(crate) fn finalize_pred(&mut self, name: String, defs: Vec<Assertion>) -> Pred {
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
            name,
            num_params: params.len(),
            params,
            abstract_: false,
            facts: vec![],
            definitions: defs,
            ins,
            pure: false,
            guard: self.guard(),
        }
    }

    pub(crate) fn compile_concrete(mut self) -> Pred {
        let name = self.pred_name();

        let pred = self.global_env.predicate(self.body_id).clone();
        let definitions = self.compile_predicate_body(pred);

        self.global_env_mut().mark_pred_as_compiled(name.clone());

        self.finalize_pred(name, definitions)
    }

    /// Returns a tuple of universally quantified lvars, precondition, (existentially quantified lvars, postcondition, trusted)
    pub(crate) fn raw_spec(
        mut self,
    ) -> (
        IndexMap<Symbol, Ty<'tcx>>,
        Assertion,
        Vec<(Vec<(Symbol, Ty<'tcx>)>, Assertion)>,
        bool,
    ) {
        let SpecTerm {
            uni,
            pre,
            posts,
            trusted,
        } = self
            .global_env
            .gilsonite_spec(self.body_id)
            .unwrap()
            .clone();

        let pre = self.compile_assertion(pre);

        let posts = posts
            .into_iter()
            .map(|(exi, post)| (exi, self.compile_assertion(post)))
            .collect();

        (uni.into_iter().collect(), pre, posts, trusted)
        // (uni.into_iter().collect(), pre, (exi, post))
    }

    pub fn compile_formula(&mut self, formula: gilsonite::Formula<'tcx>) -> Formula {
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
                let left = Box::new(self.compile_expression(*left));
                let right = Box::new(self.compile_expression(*right));
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

    pub fn compile_expression(&mut self, body: gilsonite::Expr<'tcx>) -> GExpr {
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
                params.extend(args.into_iter().map(|e| self.compile_expression(e)));

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
                let left = self.compile_expression(*left);
                let right = self.compile_expression(*right);
                match op {
                    BinOp::Eq => GExpr::eq_expr(left, right),
                    BinOp::Lt => {
                        if left_ty.is_integral() {
                            GExpr::i_lt(left, right)
                        } else {
                            GExpr::f_lt(left, right)
                        }
                    }
                    BinOp::Le => {
                        if left_ty.is_integral() {
                            GExpr::i_le(left, right)
                        } else {
                            GExpr::f_le(left, right)
                        }
                    }
                    BinOp::Ne => GExpr::e_not(GExpr::eq_expr(left, right)),
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
                    BinOp::Rem => {
                        if left_ty.is_integral() {
                            GExpr::BinOp {
                                operator: gillian::gil::BinOp::IMod,
                                left_operand: Box::new(left),
                                right_operand: Box::new(right),
                            }
                        } else {
                            todo!("Non-integral rem")
                        }
                    }
                    BinOp::Shl => {
                        if left_ty.is_integral() {
                            GExpr::i_shl(left, right)
                        } else {
                            todo!("shl for floats")
                        }
                    }
                    BinOp::Div => {
                        if left_ty.is_integral() {
                            GExpr::i_div(left, right)
                        } else {
                            GExpr::f_div(left, right)
                        }
                    }
                    BinOp::And => GExpr::and(left, right),
                    BinOp::Or => GExpr::or(left, right),
                    BinOp::Impl => GExpr::implies(left, right),
                    BinOp::Ge => {
                        if left_ty.is_integral() {
                            GExpr::i_ge(left, right)
                        } else {
                            GExpr::f_ge(left, right)
                        }
                    }
                    BinOp::Gt => {
                        if left_ty.is_integral() {
                            GExpr::i_gt(left, right)
                        } else {
                            GExpr::f_gt(left, right)
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
                    .map(|f| self.compile_expression(f))
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
                    .map(|f| self.compile_expression(f))
                    .collect();
                fields.into()
            }
            ExprKind::Field { lhs, field } => {
                if matches!(lhs.ty.kind(), TyKind::Tuple(..)) {
                    self.compile_expression(*lhs).lnth(field.as_u32())
                } else if lhs.ty.is_any_ptr() {
                    let ty = lhs.ty.builtin_deref(true).unwrap().ty;
                    let gil_derefed = self.compile_expression(*lhs);
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
                                let lhs = self.compile_expression(*lhs);
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

            ExprKind::Integer { value } => value.0.into(),
            ExprKind::True => GExpr::Lit(Literal::Bool(true)),
            ExprKind::False => GExpr::Lit(Literal::Bool(false)),
            ExprKind::SeqNil => GExpr::EList(vec![]),
            ExprKind::SeqOp { op, args } => {
                let mut args: Vec<_> = args
                    .into_iter()
                    .map(|a| self.compile_expression(a))
                    .collect();
                match op {
                    SeqOp::Append => args.remove(0).lst_concat(vec![args.remove(0)].into()),
                    SeqOp::Prepend => {
                        GExpr::lst_concat(vec![args.remove(1)].into(), args.remove(0))
                    }
                    SeqOp::Concat => args.remove(0).lst_concat(args.remove(0)),
                    SeqOp::Head => args.remove(0).lst_head(),
                    SeqOp::Last => args.remove(0).lst_last(),
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
                let mut_ref = self.compile_expression(*mut_ref);
                let pcy = self.compile_expression(*prophecy);
                [mut_ref.lnth(0), pcy].into()
            }
            ExprKind::GetProphecy { mut_ref } => {
                self.assert_prophecies_enabled("using `Prophecised::prophecy`");
                let mut_ref = self.compile_expression(*mut_ref);
                mut_ref.lnth(1)
            }
            ExprKind::GetValue { mut_ref } => {
                self.assert_prophecies_enabled("using `Prophecy::value`");
                let ty = self
                    .tcx()
                    .try_normalize_erasing_regions(self.param_env, mut_ref.ty)
                    .unwrap_or(mut_ref.ty);
                let ty = self.unwrap_prophecy_ty(ty);
                let prophecy = self.compile_expression(*mut_ref);
                let value = self.temp_lvar(ty);
                self.local_toplevel_asrts
                    .push(core_preds::pcy_value(prophecy, value.clone()));
                value
            }
            ExprKind::Exists { var, body } => {
                let ty = gil_type_of_rust_ty(var.1);
                GExpr::EExists(
                    vec![(var.0.to_string(), ty)],
                    Box::new(self.compile_expression(*body)),
                )
            }
            ExprKind::EForall { var, body } => {
                let ty = gil_type_of_rust_ty(var.1);
                GExpr::EForall(
                    vec![(var.0.to_string(), ty)],
                    Box::new(self.compile_expression(*body)),
                )
            }

            ExprKind::UnOp { op, arg } => {
                let arg = self.compile_expression(*arg);

                match op {
                    mir::UnOp::Not => arg.e_not(),
                    mir::UnOp::Neg => GExpr::minus(GExpr::int(0), arg),
                }
            }
            ExprKind::PtrToMutRef { ptr } => {
                if self.prophecies_enabled() {
                    GExpr::EList(vec![self.compile_expression(*ptr), Expr::null()])
                } else {
                    self.compile_expression(*ptr)
                }
            }
        }
    }
}

pub fn gil_type_of_rust_ty(ty: Ty) -> Option<Type> {
    match ty.kind() {
        TyKind::Bool => Some(Type::BoolType),
        TyKind::Int(_) | TyKind::Uint(_) => Some(Type::IntType),
        TyKind::Float(_) => Some(Type::NumberType),
        TyKind::Tuple(_) | TyKind::Array(..) => Some(Type::ListType),
        _ => None,
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
