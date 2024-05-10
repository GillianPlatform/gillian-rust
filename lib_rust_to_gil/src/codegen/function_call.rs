use std::collections::HashMap;

use crate::logic::builtins::FnStubs;
use crate::logic::param_collector;
use crate::prelude::*;
use names::bb_label;
use rustc_middle::ty::{GenericArgKind, GenericArgsRef, PolyFnSig, Region};
use rustc_span::source_map::Spanned;
use rustc_target::abi::VariantIdx;

use super::typ_encoding::lifetime_param_name;

enum ConstructorKind {
    Enum(VariantIdx),
}

enum CallKind {
    Constructor(ConstructorKind),
    Lemma(String),
    MonoFn(String),
    PolyFn(String),
    Unfold(String),
    Fold(String),
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn identify_call_kind(&mut self, did: DefId, substs: GenericArgsRef<'tcx>) -> CallKind {
        let fname = self.tcx().def_path_str_with_args(did, substs);

        let stub = FnStubs::of_def_id(did, self.tcx());
        log::trace!("Shimming {}, stub is {:?}", fname, stub);
        match stub {
            Some(FnStubs::Into)
                if substs.type_at(0).is_ref()
                    && crate::utils::ty::is_nonnull(substs.type_at(1), self.tcx()) =>
            {
                CallKind::PolyFn("<&mut T std::convert::Into<U>>::into".into())
            }
            Some(FnStubs::Into)
                if crate::utils::ty::is_unique(substs.type_at(0), self.tcx())
                    && crate::utils::ty::is_nonnull(substs.type_at(1), self.tcx()) =>
            {
                let name =
                    "<std::ptr::Unique<T> as std::convert::Into<std::ptr::NonNull<T>>>::into"
                        .into();
                CallKind::PolyFn(name)
            }
            Some(FnStubs::FoldSomething) => {
                let name = fname.strip_suffix("_____fold").unwrap().to_string();
                CallKind::Fold(name)
            }
            Some(FnStubs::UnfoldSomething) => {
                let name = fname.strip_suffix("_____unfold").unwrap().to_string();
                CallKind::Unfold(name)
            }
            Some(FnStubs::MutRefProphecyAutoUpdate) => {
                let name = self.global_env_mut().register_pcy_auto_update(substs);
                CallKind::MonoFn(name)
            }
            Some(FnStubs::MutRefResolve) => {
                let name = self.global_env_mut().register_resolver(substs);
                CallKind::MonoFn(name)
            }
            _ if crate::utils::attrs::is_lemma(did, self.tcx()) => {
                let lemma_name = self.global_env.just_pred_name_with_args(did, substs);
                CallKind::Lemma(lemma_name)
            }
            _ if self.tcx().is_constructor(did) => {
                let ty_of_ctor = self
                    .tcx()
                    .fn_sig(did)
                    .instantiate(self.tcx(), substs)
                    .output()
                    .skip_binder();
                if ty_of_ctor.is_enum() {
                    let def = ty_of_ctor.ty_adt_def().unwrap();
                    let idx = def.variant_index_with_id(did);
                    CallKind::Constructor(ConstructorKind::Enum(idx))
                } else {
                    fatal!(
                        self,
                        "Constructor function that is not for an enum: {}",
                        fname
                    );
                }
            }
            _ => CallKind::PolyFn(self.tcx().def_path_str(did)),
        }
    }

    fn all_args_for_fn_call(
        &mut self,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        operands: &[Spanned<Operand<'tcx>>],
    ) -> Vec<Expr> {
        let callee_has_regions = operands.iter().any(|op| self.operand_ty(&op.node).is_ref());
        let mut args =
            Vec::with_capacity((callee_has_regions as usize) + substs.len() + operands.len());
        if callee_has_regions {
            let sig = self.tcx().fn_sig(def_id);
            let ssig = sig.instantiate(self.tcx(), substs);
            let regions = self.check_func_call(ssig, operands);

            args.extend(
                regions
                    .into_iter()
                    .map(|r| r.as_var())
                    .map(|v| self.region_info.name_region(v))
                    .map(Expr::PVar),
            );
        }
        for ty_arg in substs {
            if let Some(e) = self.encode_generic_arg(ty_arg) {
                args.push(e.into())
            }
        }
        for op in operands {
            let op = self.push_encode_operand(&op.node);
            args.push(op)
        }
        args
    }

    pub fn only_param_args_for_fn_call(
        &mut self,
        substs: GenericArgsRef<'tcx>,
        operands: &[Spanned<Operand<'tcx>>],
    ) -> Vec<Expr> {
        let params = param_collector::collect_params_on_args(substs);
        let callee_has_regions =
            params.regions || operands.iter().any(|op| self.operand_ty(&op.node).is_ref());
        let mut args = Vec::with_capacity(
            (callee_has_regions as usize) + params.parameters.len() + operands.len(),
        );
        if callee_has_regions {
            args.push(Expr::PVar(lifetime_param_name("a")))
        }
        for ty_arg in params.parameters {
            args.push(self.encode_type(ty_arg).into())
        }
        for op in operands {
            let op = self.push_encode_operand(&op.node);
            args.push(op)
        }
        args
    }

    pub fn check_func_call(
        &mut self,
        sig: PolyFnSig<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
    ) -> Vec<Region<'tcx>> {
        let mut tbl = HashMap::new();
        for (sig_in, arg) in sig.skip_binder().inputs().iter().zip(args) {
            let arg_ty = arg.node.ty(self.mir(), self.tcx());
            poor_man_unification(&mut tbl, *sig_in, arg_ty).unwrap();
        }

        eprintln!("{sig:?}");

        for (s, a) in &tbl {
            eprintln!("{s:?} -> {:?}", self.region_info.name_region(a.as_var()));
        }

        tbl.values().copied().collect()
    }

    pub fn push_function_call(
        &mut self,
        func: &Operand<'tcx>,
        operands: &[Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        target: Option<BasicBlock>,
    ) {
        // TODO: Handle cleanups at some point
        let (def_id, substs) = func
            .const_fn_def()
            .expect("func of functioncall isn't const_fn_def");

        let call_kind = self.identify_call_kind(def_id, substs);

        match call_kind {
            CallKind::Lemma(fname) => {
                let gil_args = self.all_args_for_fn_call(def_id, substs, operands);
                let call = Cmd::Logic(LCmd::SL(SLCmd::ApplyLem {
                    lemma_name: fname,
                    parameters: gil_args,
                    existentials: vec![],
                }));
                self.push_cmd(call);
            }
            CallKind::Fold(fname) => {
                let gil_args = self.only_param_args_for_fn_call(substs, operands);
                let call = Cmd::Logic(LCmd::SL(SLCmd::Fold {
                    pred_name: fname,
                    parameters: gil_args,
                    bindings: None,
                }));
                self.push_cmd(call);
            }
            CallKind::Unfold(fname) => {
                let gil_args = self.only_param_args_for_fn_call(substs, operands);
                let call = Cmd::Logic(LCmd::SL(SLCmd::Unfold {
                    pred_name: fname,
                    parameters: gil_args,
                    bindings: None,
                    rec: false,
                }));
                self.push_cmd(call);
            }
            CallKind::PolyFn(fname) => {
                let gil_args = self.all_args_for_fn_call(def_id, substs, operands);
                let ivar = self.temp_var();
                let call = Cmd::Call {
                    variable: ivar.clone(),
                    proc_ident: fname.into(),
                    parameters: gil_args,
                    error_lab: None,
                    bindings: None,
                };
                self.push_cmd(call);
                let call_ret_ty = self.place_ty(destination).ty;
                self.push_place_write(destination, Expr::PVar(ivar), call_ret_ty);
            }
            CallKind::MonoFn(fname) => {
                let gil_args = self.only_param_args_for_fn_call(substs, operands);
                let ivar = self.temp_var();
                let call = Cmd::Call {
                    variable: ivar.clone(),
                    proc_ident: fname.into(),
                    parameters: gil_args,
                    error_lab: None,
                    bindings: None,
                };
                self.push_cmd(call);
                let call_ret_ty = self.place_ty(destination).ty;
                self.push_place_write(destination, Expr::PVar(ivar), call_ret_ty);
            }
            CallKind::Constructor(ConstructorKind::Enum(idx)) => {
                let operands: Vec<Expr> = operands
                    .iter()
                    .map(|op| self.push_encode_operand(&op.node))
                    .collect();
                let value = vec![idx.as_u32().into(), operands.into()].into();
                self.push_place_write(destination, value, self.place_ty(destination).ty)
            }
        }
        if let Some(bb) = target {
            self.push_cmd(Cmd::Goto(bb_label(bb)));
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum PoorManUnificationError<'tcx> {
    /// Unclear what rules should apply to dyn objects
    DynObject,
    /// Too lazy to implement closures for the moment given that gillian-rust doesn't support them anyways
    ClosureOrGenerator,
    /// I don't understand how these actually work and what we need to do here
    BoundVar,
    /// Currently we don't do normalization so lets just error out here.
    Alias,
    /// General error for when we don't have types of the same shape
    Mismatch(Ty<'tcx>, Ty<'tcx>),
}

type PoorManUnificationResult<'tcx, T> = Result<T, PoorManUnificationError<'tcx>>;

pub fn poor_man_unification<'tcx>(
    tbl: &mut HashMap<Region<'tcx>, Region<'tcx>>,
    lhs: Ty<'tcx>,
    rhs: Ty<'tcx>,
) -> PoorManUnificationResult<'tcx, ()> {
    match (lhs.kind(), rhs.kind()) {
        (TyKind::Bool, TyKind::Bool) => Ok(()),
        (TyKind::Char, TyKind::Char) => Ok(()),
        (TyKind::Int(_), TyKind::Int(_)) => Ok(()),
        (TyKind::Uint(_), TyKind::Uint(_)) => Ok(()),
        (TyKind::Float(_), TyKind::Float(_)) => Ok(()),
        (TyKind::Adt(i, s), TyKind::Adt(j, t)) if i == j => {
            for (s, t) in s.into_iter().zip(t.into_iter()) {
                match (s.unpack(), t.unpack()) {
                    (GenericArgKind::Lifetime(l), GenericArgKind::Lifetime(j)) => {
                        if *tbl.entry(l).or_insert(j) != j {
                            return Err(PoorManUnificationError::Mismatch(lhs, rhs));
                        }
                    }
                    (GenericArgKind::Type(t), GenericArgKind::Type(u)) => {
                        poor_man_unification(tbl, t, u)?
                    }
                    (GenericArgKind::Const(_), GenericArgKind::Const(_)) => {}
                    _ => unreachable!("expected and provided subst don't have same shape"),
                }
            }
            Ok(())
        }
        (TyKind::Foreign(_), TyKind::Foreign(_)) => Ok(()),
        (TyKind::Str, TyKind::Str) => Ok(()),
        (TyKind::Array(t, _), TyKind::Array(u, _)) => poor_man_unification(tbl, *t, *u),
        (TyKind::Slice(t), TyKind::Slice(u)) => poor_man_unification(tbl, *t, *u),
        (TyKind::RawPtr(t, _), TyKind::RawPtr(u, _)) => poor_man_unification(tbl, *t, *u),
        (TyKind::Ref(r, t, _), TyKind::Ref(s, u, _)) => {
            if *tbl.entry(*r).or_insert(*s) != *s {
                return Err(PoorManUnificationError::Mismatch(lhs, rhs));
            }

            poor_man_unification(tbl, *t, *u)
        }
        (TyKind::FnDef(_, _), TyKind::FnDef(_, _)) if lhs == rhs => Ok(()),
        (TyKind::FnPtr(i), TyKind::FnPtr(j)) if i == j => Ok(()),
        (TyKind::Dynamic(_, _, _), TyKind::Dynamic(_, _, _)) => {
            Err(PoorManUnificationError::DynObject)
        }
        (TyKind::Closure(_, _), TyKind::Closure(_, _)) => {
            Err(PoorManUnificationError::ClosureOrGenerator)
        }
        (TyKind::Coroutine(_, _), TyKind::Coroutine(_, _)) => {
            Err(PoorManUnificationError::ClosureOrGenerator)
        }
        (TyKind::CoroutineWitness(_, _), TyKind::CoroutineWitness(_, _)) => {
            Err(PoorManUnificationError::ClosureOrGenerator)
        }
        (TyKind::Never, TyKind::Never) => Ok(()),
        (TyKind::Tuple(ts), TyKind::Tuple(us)) => ts
            .iter()
            .zip(us.iter())
            .try_for_each(|(t, u)| poor_man_unification(tbl, t, u)),
        (TyKind::Alias(_, _), TyKind::Alias(_, _)) => Err(PoorManUnificationError::Alias),
        (TyKind::Param(p), TyKind::Param(q)) if p == q => Ok(()),
        (TyKind::Bound(_, _), TyKind::Bound(_, _)) => Err(PoorManUnificationError::BoundVar),
        (TyKind::Placeholder(p), TyKind::Placeholder(q)) if p == q => Ok(()),
        (TyKind::Infer(i), TyKind::Infer(j)) if i == j => Ok(()),
        (TyKind::Error(e), TyKind::Error(f)) if e == f => Ok(()),
        _ => Err(PoorManUnificationError::Mismatch(lhs, rhs)),
    }
}
