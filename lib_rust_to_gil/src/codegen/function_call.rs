use crate::logic::builtins::FnStubs;
use crate::logic::param_collector;
use crate::prelude::*;
use crate::signature::build_signature;
use crate::utils::polymorphism::{all_generics, HasGenericArguments};
use names::bb_label;
use rustc_infer::infer::outlives::env::OutlivesEnvironment;
use rustc_infer::infer::{DefineOpaqueTypes, InferCtxt, RegionVariableOrigin, TyCtxtInferExt};
use rustc_infer::traits::ObligationCause;
use rustc_middle::ty::{self, BoundRegion, GenericArgsRef, PolyFnSig};
use rustc_span::{sym, DUMMY_SP};
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
        operands: &[Operand<'tcx>],
    ) -> Vec<Expr> {
        let callee_has_regions = operands.iter().any(|op| self.operand_ty(op).is_ref());
        let mut args =
            Vec::with_capacity((callee_has_regions as usize) + substs.len() + operands.len());
        if callee_has_regions {
            let callee_sig = build_signature(self.global_env, def_id);
            eprintln!(
                "callee_has_regions {def_id:?}, {substs:?} {:?}",
                self.tcx().fn_sig(def_id)
            );
            let mut infcx = self.tcx().infer_ctxt().build();
            self.check_func_call(&mut infcx, self.tcx().fn_sig(def_id).skip_binder(), operands);
            if self.has_generic_lifetimes() {
                eprintln!("has_generic_lifetimes {substs:?}");
                args.push(Expr::PVar(lifetime_param_name("a")))
            } else {
                args.push(Expr::null())
            }
        }
        for ty_arg in substs {
            if let Some(e) = self.encode_generic_arg(ty_arg) {
                args.push(e.into())
            }
        }
        for op in operands {
            let op = self.push_encode_operand(op);
            args.push(op)
        }
        args
    }

    pub fn only_param_args_for_fn_call(
        &mut self,
        substs: GenericArgsRef<'tcx>,
        operands: &[Operand<'tcx>],
    ) -> Vec<Expr> {
        let params = param_collector::collect_params_on_args(substs);
        let callee_has_regions =
            params.regions || operands.iter().any(|op| self.operand_ty(op).is_ref());
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
            let op = self.push_encode_operand(op);
            args.push(op)
        }
        args
    }

    pub fn check_func_call(
        &mut self,
        infcx: &mut InferCtxt<'tcx>,
        sig: PolyFnSig<'tcx>,
        args: &[Operand<'tcx>],
    ) {
        let tcx = self.tcx();
        let (unnormalized_sig, map) = tcx.replace_late_bound_regions(sig, |br| {
            // use renumber::RegionCtxt;

            // let region_ctxt_fn = || {
            //     let reg_info = match br.kind {
            //         ty::BoundRegionKind::BrAnon => sym::anon,
            //         ty::BoundRegionKind::BrNamed(_, name) => name,
            //         ty::BoundRegionKind::BrEnv => sym::env,
            //     };

            //     rustc_borrowck::
            //     RegionCtxt::LateBound(reg_info)
            // };

            infcx.next_region_var(
                // TODO(xavier): change this to a real origin?
                RegionVariableOrigin::MiscVariable(DUMMY_SP),
                // rustc_infer::infer::RegionVariableOrigin::LateBoundRegion((), (), ())
                // BoundRegion(DUMMY_SP, br.kind, BoundRegionConversionTime::FnCall),
                // region_ctxt_fn,
            )
        });

        eprintln!("{map:?}");

        for (sig_in, arg) in unnormalized_sig.inputs().iter().zip(args) {
            let arg_ty = arg.ty(self.mir(), self.tcx());
            // TODO(xavier) is this correct? who knows!
            eprintln!("{arg_ty:?} <: {sig_in:?}");
            let res = infcx
                .at(&ObligationCause::dummy(), self.tcx().param_env(self.did()))
                .relate(DefineOpaqueTypes::No, *sig_in, ty::Variance::Contravariant, arg_ty).unwrap();
            assert!(res.obligations.is_empty());
        }

        let _ = infcx.resolve_regions(&OutlivesEnvironment::new(self.tcx().param_env(self.did())));

        // eprintln!("{:?}", infcx.unresolved_variables());
        for (k, v) in map {
            eprintln!("{k:?} -> {v:?}");

            let r = infcx.fully_resolve(v);

            eprintln!("{r:?}");
        }

        // infcx.

    }

    pub fn push_function_call(
        &mut self,
        func: &Operand<'tcx>,
        operands: &[Operand<'tcx>],
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
                eprintln!(
                    "PolyFn call {def_id:?} {:?}",
                    all_generics(self.tcx(), def_id)
                );
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
                    .map(|op| self.push_encode_operand(op))
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
