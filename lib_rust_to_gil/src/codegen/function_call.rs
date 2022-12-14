use crate::prelude::*;
use names::bb_label;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::{GenericArg, GenericArgKind, List};

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn encode_generic_arg(&mut self, arg: GenericArg<'tcx>) -> Option<EncodedType> {
        match arg.unpack() {
            // We don't make use of Lifetime arguments for now
            GenericArgKind::Lifetime(..) => None,
            GenericArgKind::Const(..) => fatal!(
                self,
                "unhandled yet: Cannot compile function with const param"
            ),
            GenericArgKind::Type(ty) => Some(self.encode_type(ty)),
        }
    }

    fn shim(&mut self, fname: &str, substs: &List<GenericArg>) -> Option<String> {
        // The matching should probably be perfomed on the `def_path`
        // instead of the `def_path_str`.
        // This is a quick hack for now.
        match fname {
            "std::convert::Into::into" => {
                if let TyKind::Ref(_, ty, Mutability::Mut) = substs[0].expect_ty().kind() {
                    if let TyKind::Adt(adt_def, subst) = substs[1].expect_ty().kind() {
                        if let "core::ptr::NonNull" | "std::ptr::NonNull" =
                            self.tcx.def_path_str(adt_def.did()).as_str()
                        {
                            if subst[0].expect_ty() == *ty {
                                return Some("mut_ref_to_nonnull_ptr".to_string());
                            }
                        }
                    }
                };
                None
            }
            _ => None,
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

        let fname = with_no_trimmed_paths!(self.tcx.def_path_str(def_id));
        let fname = self.shim(&fname, substs).unwrap_or(fname);
        let mut gil_args = Vec::with_capacity(args.len() + substs.len());
        for tyarg in substs.iter().filter_map(|a| self.encode_generic_arg(a)) {
            gil_args.push(tyarg.into())
        }
        for arg in args {
            gil_args.push(self.push_encode_operand(arg));
        }
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
