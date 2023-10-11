use crate::logic::core_preds;
use crate::logic::traits::TraitSolver;
use crate::prelude::*;
use crate::utils::polymorphism::HasGenericLifetimes;
use names::bb_label;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{GenericArg, GenericArgsRef};

use super::typ_encoding::lifetime_param_name;

enum Shim {
    Lemma(String),
    Function(String),
    Unfold(String),
    Fold(String),
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn shim(&self, did: DefId, substs: GenericArgsRef<'tcx>, arg_tys: &[Ty<'tcx>]) -> Option<Shim> {
        // The matching should probably be perfomed on the `def_path`
        // instead of the `def_path_str`.
        // This is a quick hack for now.
        let fname = self.tcx().def_path_str(did);
        log::debug!("Shimming {}", fname);
        match fname.as_str() {
            "std::convert::Into::into" => {
                if let TyKind::Ref(_, ty, Mutability::Mut) = substs[0].expect_ty().kind() {
                    if let TyKind::Adt(adt_def, subst) = substs[1].expect_ty().kind() {
                        if let "core::ptr::NonNull" | "std::ptr::NonNull" =
                            self.tcx().def_path_str(adt_def.did()).as_str()
                        {
                            if subst[0].expect_ty() == *ty {
                                return Some(Shim::Function("mut_ref_to_nonnull_ptr".to_string()));
                            }
                        }
                    }
                };
                None
            }
            "gilogic::Ownable::ref_mut_inner_____unfold" => {
                if ty_utils::is_ty_param(substs[0].expect_ty()) {
                    Some(Shim::Lemma("$POLYMORPHIC::ref_mut_inner_open".to_string()))
                } else {
                    None
                }
            }
            "gilogic::Ownable::ref_mut_inner_____fold" => {
                if ty_utils::is_ty_param(substs[0].expect_ty()) {
                    Some(Shim::Lemma("$POLYMORPHIC::ref_mut_inner_close".to_string()))
                } else {
                    None
                }
            }
            "gilogic::Ownable::own_____unfold" => {
                let generic_args: Vec<GenericArg<'_>> =
                    arg_tys.iter().map(|x| (*x).into()).collect();
                let arg_tys = self.tcx().mk_args(&generic_args);
                let name = self
                    .tcx()
                    .def_path_str_with_args(did, arg_tys)
                    .strip_suffix("_____unfold")
                    .unwrap()
                    .to_string();
                Some(Shim::Unfold(name))
            }

            "gilogic::Ownable::own_____fold" => {
                let generic_args: Vec<GenericArg<'_>> =
                    arg_tys.iter().map(|x| (*x).into()).collect();
                let arg_tys = self.tcx().mk_args(&generic_args);
                let name = self
                    .tcx()
                    .def_path_str_with_args(did, arg_tys)
                    .strip_suffix("_____fold")
                    .unwrap()
                    .to_string();
                Some(Shim::Fold(name))
            }
            _ if crate::utils::attrs::is_lemma(did, self.tcx()) => {
                Some(Shim::Lemma(fname.to_string()))
            }
            other => other
                .strip_suffix("_____unfold")
                .map(|name| Shim::Unfold(name.to_string()))
                .or_else(|| {
                    other
                        .strip_suffix("_____fold")
                        .map(|name| Shim::Fold(name.to_string()))
                }),
        }
    }

    fn push_prophecy_auto_update(&mut self, args: &[Operand<'tcx>], destination: Place<'tcx>) {
        assert_eq!(args.len(), 1);
        assert!(self.global_env.config.prophecies);
        let mutref = &args[0];
        let mutref_ty = self.operand_ty(mutref);
        let inner_ty = ty_utils::mut_ref_inner(mutref_ty)
            .expect("Calling prophecy_auto_update on something that isn't a mutref");
        let pointee = Expr::LVar(self.temp_lvar());
        let new_repr = self.temp_lvar();
        let mutref = self.push_encode_operand(mutref);
        let pointer = mutref.clone().lnth(0);
        let pcy = mutref.lnth(1);
        let value_cp = core_preds::value(pointer, self.encode_type(inner_ty), pointee.clone());
        let (own_instance_did, own_instance_subst) = self.global_env.get_own_pred_for(inner_ty);
        let own_pred_name = self.tcx().def_path_str(own_instance_did);
        let generic_args = own_instance_subst
            .into_iter()
            .filter_map(|arg| self.encode_generic_arg(arg).map(|x| x.into()));
        let own_pred_call = Assertion::Pred {
            name: own_pred_name,
            params: generic_args
                .chain([pointee, Expr::LVar(new_repr.clone())])
                .collect(),
        };
        let asrt_cmd = Cmd::slcmd(SLCmd::SepAssert {
            assertion: value_cp.star(own_pred_call),
            existentials: vec![new_repr.clone()],
        });
        let repr_ty_id = self
            .tcx()
            .get_diagnostic_item(Symbol::intern("gillian::pcy::ownable::representation_ty"))
            .expect("Couldn't find gillian::ownable::representation_ty");
        let repr_ty = self.resolve_associated_type(repr_ty_id, inner_ty);
        let pcy_assign = crate::codegen::memory::MemoryAction::PcyAssign {
            pcy,
            repr_ty,
            value: Expr::LVar(new_repr),
        };
        let pcy_temp = self.temp_var();
        self.push_cmd(asrt_cmd);
        self.push_action(pcy_temp, pcy_assign);
        self.push_place_write(destination, vec![].into(), self.place_ty(destination).ty);
    }

    fn push_prophecy_resolve(
        &mut self,
        args: &[Operand<'tcx>],
        destination: Place<'tcx>,
        lft_param: Expr,
    ) {
        assert_eq!(args.len(), 1);
        assert!(self.global_env.config.prophecies);
        let mutref = &args[0];
        let mutref_ty = self.operand_ty(mutref);
        let mutref = self.push_encode_operand(mutref);
        let (resolver, subst) = self.global_env.add_resolver(mutref_ty);
        let parameters: Vec<_> = std::iter::once(lft_param)
            .chain(
                subst
                    .iter()
                    .filter_map(|arg| self.encode_generic_arg(arg).map(|x| x.into())),
            )
            .chain(std::iter::once(mutref))
            .collect();
        let variable = self.temp_var();
        let cmd = Cmd::Call {
            variable: variable.clone(),
            proc_ident: Expr::string(resolver),
            parameters,
            error_lab: None,
            bindings: None,
        };
        self.push_cmd(cmd);
        self.push_place_write(
            destination,
            Expr::PVar(variable),
            self.place_ty(destination).ty,
        );
    }

    // fn

    pub fn push_function_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: Place<'tcx>,
        target: Option<BasicBlock>,
    ) {
        // TODO: Handle cleanups at some point
        let (def_id, substs) = func
            .const_fn_def()
            .expect("func of functioncall isn't const_fn_def");

        if self.tcx().is_constructor(def_id) {
            let args = args
                .iter()
                .map(|x| self.push_encode_operand(x))
                .collect::<Vec<_>>();
            let ty_of_ctor = self
                .tcx()
                .fn_sig(def_id)
                .instantiate(self.tcx(), substs)
                .output()
                .skip_binder();
            if ty_of_ctor.is_enum() {
                let def = ty_of_ctor.ty_adt_def().unwrap();
                let idx = def.variant_index_with_ctor_id(def_id);
                let value = vec![idx.as_u32().into(), args.into()].into();
                self.push_place_write(destination, value, self.place_ty(destination).ty);
                if let Some(bb) = target {
                    self.push_cmd(Cmd::Goto(bb_label(bb)));
                }
                return;
            }
        }

        if (self
            .tcx()
            .is_diagnostic_item(Symbol::intern("gillian::ownable::own::open"), def_id)
            || self
                .tcx()
                .is_diagnostic_item(Symbol::intern("gillian::ownable::own::close"), def_id))
            && ty_utils::is_mut_ref(self.operand_ty(&args[0]))
        {
            let arg_ty = self.operand_ty(&args[0]);
            let name = self.global_env.add_mut_ref_own(arg_ty);
            let inner_ty = ty_utils::mut_ref_inner(arg_ty).unwrap();
            let own_did = self
                .tcx()
                .get_diagnostic_item(Symbol::intern("gillian::ownable::own"))
                .expect("You need to import gilogic");
            let (_, substs) =
                self.resolve_candidate(own_did, self.tcx().mk_args(&[inner_ty.into()]));
            let mut gil_args = vec![Expr::PVar(lifetime_param_name(
                &self.generic_lifetimes()[0],
            ))];
            for tyarg in substs.iter().filter_map(|a| self.encode_generic_arg(a)) {
                gil_args.push(tyarg.into())
            }
            for arg in args {
                gil_args.push(self.push_encode_operand(arg));
            }
            let cmd = if self
                .tcx()
                .is_diagnostic_item(Symbol::intern("gillian::ownable::own::open"), def_id)
            {
                Cmd::Logic(LCmd::SL(SLCmd::Unfold {
                    pred_name: name,
                    parameters: gil_args,
                    bindings: None,
                    rec: false,
                }))
            } else {
                Cmd::Logic(LCmd::SL(SLCmd::Fold {
                    pred_name: name,
                    parameters: gil_args,
                    bindings: None,
                }))
            };

            self.push_cmd(cmd);
            return;
        }

        let fname = with_no_trimmed_paths!(self.tcx().def_path_str(def_id));

        match fname.as_str() {
            "gilogic::prophecies::Prophecised::prophecy_auto_update" => {
                self.push_prophecy_auto_update(args, destination);
                return;
            }
            "gilogic::prophecies::Prophecised::prophecy_resolve" => {
                let self_lifetimes = self.generic_lifetimes();
                let lft_param = if self_lifetimes.len() == 1 {
                    Expr::PVar(lifetime_param_name(&self_lifetimes[0]))
                } else {
                    fatal!(self, "Cannot handle lifetimes in function call properly")
                };
                self.push_prophecy_resolve(args, destination, lft_param);
                return;
            }
            _ => {}
        };

        let arg_tys = args.iter().map(|x| self.operand_ty(x)).collect::<Vec<_>>();
        let shim = self
            .shim(def_id, substs, &arg_tys)
            .unwrap_or(Shim::Function(fname));
        let mut gil_args = Vec::with_capacity(args.len() + substs.len());

        // Big hack, to handle lifetimes. I need to figure out the proper mapping.
        // That's where Polonius should help.
        // For now, we only handle the case where the callee has 1 or 0 lifetimes, and the caller has 1 or 0 lifetimes,
        // We assume they are the same (which is sound though over-approximating)
        let self_lifetimes = self.generic_lifetimes();
        let callee_lifetimes = (def_id, self.tcx()).generic_lifetimes();
        if self_lifetimes.len() == 1 && callee_lifetimes.len() == 1 {
            gil_args.push(Expr::PVar(lifetime_param_name(&self_lifetimes[0])));
        } else if callee_lifetimes.is_empty() {
            // Do nothing
        } else {
            fatal!(self, "Cannot handle lifetimes in function call properly")
        }

        for tyarg in substs.iter().filter_map(|a| self.encode_generic_arg(a)) {
            gil_args.push(tyarg.into())
        }
        for arg in args {
            gil_args.push(self.push_encode_operand(arg));
        }
        match shim {
            Shim::Lemma(fname) => {
                let call = Cmd::Logic(LCmd::SL(SLCmd::ApplyLem {
                    lemma_name: fname,
                    parameters: gil_args,
                    existentials: vec![],
                }));
                self.push_cmd(call);
            }
            Shim::Fold(fname) => {
                let call = Cmd::Logic(LCmd::SL(SLCmd::Fold {
                    pred_name: fname,
                    parameters: gil_args,
                    bindings: None,
                }));
                self.push_cmd(call);
            }
            Shim::Unfold(fname) => {
                let call = Cmd::Logic(LCmd::SL(SLCmd::Unfold {
                    pred_name: fname,
                    parameters: gil_args,
                    bindings: None,
                    rec: false,
                }));
                self.push_cmd(call);
            }
            Shim::Function(fname) => {
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
        }
        if let Some(bb) = target {
            self.push_cmd(Cmd::Goto(bb_label(bb)));
        }
    }
}
