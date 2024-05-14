use std::collections::HashMap;

use super::gilsonite;
use super::utils::get_thir;
use super::{builtins::LogicStubs, is_borrow};
use crate::logic::gilsonite::SeqOp;
use crate::signature::{build_signature, Signature};
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

use rustc_middle::{
    thir::{BlockId, ExprId, ExprKind, LocalVarId, PatKind, Thir},
    ty::{AdtKind, EarlyBinder},
};
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
            sig: build_signature(global_env, body_id),
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
            let lft = self.sig.lifetimes().next().unwrap();
            Some(lft.to_string()).into_iter()
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

    pub(crate) fn get_stub(&self, ty: Ty<'tcx>) -> Option<LogicStubs> {
        LogicStubs::for_fn_def_ty(ty, self.tcx())
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
        let left_ty = self.subst(src.ty);
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

    pub fn compile_assertion(&mut self, e: ExprId, thir: &Thir<'tcx>) -> Assertion {
        let gilsonite = gilsonite::GilsoniteBuilder::new(thir.clone(), self.tcx());
        let _asrt = gilsonite.build_assert(e);
        // dbg!(_asrt);
        self.compile_assertion_inner(_asrt)
        //
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
                let substs = self.subst(substs);
                let (name, substs) = self.global_env_mut().resolve_predicate(def_id, substs);

                let ty_params = param_collector::collect_params_on_args(substs)
                    .with_consider_arguments(args.iter().map(|id| self.subst(id.ty)));
                let mut params = Vec::with_capacity(
                    ty_params.parameters.len() + (ty_params.regions as usize) + args.len(),
                );
                if ty_params.regions {
                    if !has_generic_lifetimes(self.body_id, self.tcx()) {
                        fatal!(
                            self,
                            "predicate calling another one, it has a lifetime param but not self?"
                        )
                    };
                    let lft = self.sig.lifetimes().next().unwrap();

                    params.push(Expr::PVar(lft.to_string()));
                }
                for tyarg in ty_params.parameters {
                    let tyarg = self.encode_type(tyarg);
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
                let typ = self.encode_type(self.unwrap_prophecy_ty(self.subst(prophecy.ty)));
                let prophecy = self.compile_expression_inner(prophecy);
                let model = self.compile_expression_inner(model);
                super::core_preds::controller(prophecy, typ, model)
            }
            AssertKind::ProphecyObserver { prophecy, model } => {
                self.assert_prophecies_enabled("using prophecy::controller");
                let typ = self.encode_type(self.unwrap_prophecy_ty(self.subst(prophecy.ty)));
                let prophecy = self.compile_expression_inner(prophecy);
                let model = self.compile_expression_inner(model);
                super::core_preds::observer(prophecy, typ, model)
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

                let typ = self.encode_array_type(self.subst(ty), size);
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

                let Some(block) = self.resolve_block(expr, &thir) else {
                    unreachable!("closure must start with block")
                };

                assert_eq!(thir[block].stmts.len(), 0);

                k(self, thir[block].expr.unwrap(), &thir)
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
            let lft_param = self.sig.lifetimes().next().unwrap();
            Assertion::star(
                inner,
                super::core_preds::alive_lft(Expr::LVar(format!("#{lft_param}"))),
            )
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
            self.peel_lvar_bindings(ret_expr, &thir, |this, expr, thir| {
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
                let left = self.compile_expression_inner(*left);
                let right = self.compile_expression_inner(*right);
                match op {
                    BinOp::Eq => GExpr::eq_expr(left, right),
                    BinOp::Lt => todo!(),
                    BinOp::Le => todo!(),
                    BinOp::Ne => todo!(),
                    BinOp::Sub => GExpr::minus(left, right),
                    BinOp::Add => GExpr::plus(left, right),
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
                if matches!(self.subst(lhs.ty).kind(), TyKind::Tuple(..)) {
                    self.compile_expression_inner(*lhs).lnth(field.as_u32())
                } else if lhs.ty.is_any_ptr() {
                    let ty = self.subst(lhs.ty.builtin_deref(true).unwrap().ty);
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
                    match self.subst(lhs.ty).ty_adt_def() {
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

            ExprKind::Var { id } => match self.var_map.get(&id) {
                // Actually, the information about variable names is contained in
                // `self.tcx().hir().name(id.0)`. So the information I keep is redundant.
                // This deserves a cleanum.
                Some(var) => var.clone(),
                None => {
                    let name = format!("#{}", self.tcx().hir().name(id.0));
                    GExpr::LVar(name)
                }
            },
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
                let ty = self.unwrap_prophecy_ty(self.subst(mut_ref.ty));
                let prophecy = self.compile_expression_inner(*mut_ref);
                let value = self.temp_lvar(ty);
                let ty = self.encode_type(ty);
                self.local_toplevel_asrts
                    .push(core_preds::pcy_value(prophecy, ty, value.clone()));
                value
            }
        }
    }
}

fn fn_args_and_tys(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<(Symbol, Ty<'_>)> {
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
