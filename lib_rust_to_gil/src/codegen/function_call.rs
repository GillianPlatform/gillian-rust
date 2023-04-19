use crate::prelude::*;
use crate::utils::polymorphism::HasGenericLifetimes;
use names::bb_label;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{GenericArg, List};

use super::typ_encoding::lifetime_param_name;

#[derive(PartialEq, Eq)]
enum Kind {
    Lemma,
    Function,
    Unfold,
    Fold,
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn shim(&mut self, fname: &str, substs: &List<GenericArg>) -> Option<(String, Kind)> {
        // The matching should probably be perfomed on the `def_path`
        // instead of the `def_path_str`.
        // This is a quick hack for now.
        match fname {
            "std::convert::Into::into" => {
                if let TyKind::Ref(_, ty, Mutability::Mut) = substs[0].expect_ty().kind() {
                    if let TyKind::Adt(adt_def, subst) = substs[1].expect_ty().kind() {
                        if let "core::ptr::NonNull" | "std::ptr::NonNull" =
                            self.tcx().def_path_str(adt_def.did()).as_str()
                        {
                            if subst[0].expect_ty() == *ty {
                                return Some((
                                    "mut_ref_to_nonnull_ptr".to_string(),
                                    Kind::Function,
                                ));
                            }
                        }
                    }
                };
                None
            }
            "gilogic::Ownable::ref_mut_inner_____unfold" => {
                if ty_utils::is_ty_param(substs[0].expect_ty()) {
                    Some(("$POLYMORPHIC::ref_mut_inner_open".to_string(), Kind::Lemma))
                } else {
                    None
                }
            }
            "gilogic::Ownable::ref_mut_inner_____fold" => {
                if ty_utils::is_ty_param(substs[0].expect_ty()) {
                    Some(("$POLYMORPHIC::ref_mut_inner_close".to_string(), Kind::Lemma))
                } else {
                    None
                }
            }
            "gilogic::Ownable::own_____unfold" => {
                if ty_utils::is_ty_param(substs[0].expect_ty()) {
                    Some(("$POLYMORPHIC::ref_mut_open".to_string(), Kind::Lemma))
                } else {
                    None
                }
            }
            "gilogic::Ownable::own_____fold" => {
                if ty_utils::is_ty_param(substs[0].expect_ty()) {
                    Some(("$POLYMORPHIC::ref_mut_close".to_string(), Kind::Lemma))
                } else {
                    None
                }
            }
            other => other
                .strip_suffix("_____unfold")
                .map(|name| (name.to_string(), Kind::Unfold))
                .or_else(|| {
                    other
                        .strip_suffix("_____fold")
                        .map(|name| (name.to_string(), Kind::Fold))
                }),
        }
    }

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

        let fname = with_no_trimmed_paths!(self.tcx().def_path_str(def_id));
        let (fname, kind) = self.shim(&fname, substs).unwrap_or((fname, Kind::Function));
        let mut gil_args = Vec::with_capacity(args.len() + substs.len());

        // Big hack, to handle lifetimes. I need to figure out the proper mapping.
        // That's where Polonius should help.
        // For now, we only handle the case where the callee has 1 or 0 lifetimes, and the caller has 1 or 0 lifetimes,
        // We assume they are the same (which is not true)

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

        if crate::utils::attrs::is_lemma(def_id, self.tcx()) || kind == Kind::Lemma {
            let call = Cmd::Logic(LCmd::SL(SLCmd::ApplyLem {
                lemma_name: fname,
                parameters: gil_args,
                existentials: vec![],
            }));
            self.push_cmd(call);
        } else if let Kind::Fold = kind {
            let call = Cmd::Logic(LCmd::SL(SLCmd::Fold {
                pred_name: fname,
                parameters: gil_args,
                bindings: None,
            }));
            self.push_cmd(call);
        } else if let Kind::Unfold = kind {
            let call = Cmd::Logic(LCmd::SL(SLCmd::Unfold {
                pred_name: fname,
                parameters: gil_args,
                bindings: None,
                rec: false,
            }));
            self.push_cmd(call);
        } else {
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
            if let Some(bb) = target {
                self.push_cmd(Cmd::Goto(bb_label(bb)));
            }
        }
    }
}
