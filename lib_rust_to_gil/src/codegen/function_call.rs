use crate::logic::builtins::FnStubs;
use crate::logic::param_collector;
use crate::prelude::*;
use crate::utils::polymorphism::HasGenericArguments;
use names::bb_label;
use rustc_middle::ty::GenericArgsRef;
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
        log::debug!("Shimming {}, stub is {:?}", fname, stub);
        match stub {
            Some(FnStubs::Into)
                if substs.type_at(0).is_ref()
                    && crate::utils::ty::is_nonnull(substs.type_at(1), self.tcx()) =>
            {
                CallKind::PolyFn("<&mut T std::convert::Into<U>>::into".into())
            }
            // "std::convert::Into::into" => {
            //     if let TyKind::Ref(_, ty, Mutability::Mut) = substs[0].expect_ty().kind() {
            //         if let TyKind::Adt(adt_def, subst) = substs[1].expect_ty().kind() {
            //             if let "core::ptr::NonNull" | "std::ptr::NonNull" =
            //                 self.tcx().def_path_str(adt_def.did()).as_str()
            //             {
            //                 if subst[0].expect_ty() == *ty {
            //                     return Some(Shim::Function("mut_ref_to_nonnull_ptr".to_string()));
            //                 }
            //             }
            //         }
            //     };
            //     None
            // }
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
        substs: GenericArgsRef<'tcx>,
        operands: &[Operand<'tcx>],
    ) -> Vec<Expr> {
        let callee_has_regions = operands.iter().any(|op| self.operand_ty(op).is_ref());
        let mut args =
            Vec::with_capacity((callee_has_regions as usize) + substs.len() + operands.len());
        if callee_has_regions {
            if !self.has_generic_lifetimes() {
                fatal!(
                    self,
                    "{:?} doesn't have generic lifetimes, but makes a call which does. subst is {:?}, operands are {:?}",
                    self.tcx().def_path_str(self.did()),
                    substs, operands
                )
            }
            args.push(Expr::PVar(lifetime_param_name("a")))
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

    fn only_param_args_for_fn_call(
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
                let gil_args = self.all_args_for_fn_call(substs, operands);
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
                let gil_args = self.all_args_for_fn_call(substs, operands);
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
