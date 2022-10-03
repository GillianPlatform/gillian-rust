use crate::codegen::place::{ArithKind, GilProj};
use crate::prelude::*;
use names::bb_label;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_middle::ty::{print::with_no_trimmed_paths, TypeAndMut};
use rustc_span::symbol::sym;

impl<'tcx> GlobalEnv<'tcx> {
    // This should be interned instead of rebuilt every time
    // proc ptr_plus_impl_ty(p, i) {
    //    ret := {{ l-nth(p, 0i), l+ (l-nth(p, 1i), {{ {{ "+", i, ty }} }}) }};
    //    return
    // }
    pub fn ptr_plus_impl(&mut self, ty: Ty<'tcx>, fname: String) -> Proc {
        let ty = match ty.kind() {
            TyKind::RawPtr(TypeAndMut { ty, .. }) => ty,
            _ => fatal!(self, "Calling ptr::add not on a raw pointer"),
        };
        let mut body: Vec<ProcBodyItem> = vec![];
        let p = "p";
        let i = "i";
        let plus = GilProj::Plus(
            ArithKind::Overflow,
            Expr::PVar(i.into()),
            self.encode_type(*ty),
        );
        let addr = Expr::lnth(Expr::PVar(p.into()), 0);
        let proj = Expr::lnth(Expr::PVar(p.into()), 1);
        let nproj = Expr::lst_concat(proj, vec![plus.into_expr()].into());
        let ret_val = vec![addr, nproj].into();
        let assign = Cmd::Assignment {
            variable: names::ret_var(),
            assigned_expr: ret_val,
        };
        body.push(assign.into());
        body.push(Cmd::ReturnNormal.into());

        Proc {
            name: fname,
            body,
            params: vec![p.into(), i.into()],
            spec: None,
        }
    }
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn is_core(&self, krate: CrateNum) -> bool {
        matches!(self.tcx.crate_name(krate), sym::core)
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

        let fname = self.tcx.def_path_str_with_substs(def_id, substs);
        let mut gil_args = Vec::with_capacity(args.len());
        for arg in args {
            gil_args.push(self.push_encode_operand(arg));
        }
        let fname = self.shim_with(def_id, args, fname).into();
        let ivar = self.temp_var();
        self.push_cmd(Cmd::Call {
            variable: ivar.clone(),
            parameters: gil_args,
            proc_ident: fname,
            error_lab: None,
            bindings: None,
        });
        let call_ret_ty = self.place_ty(destination).ty;
        self.push_place_write(destination, Expr::PVar(ivar), call_ret_ty);
        if let Some(bb) = target {
            self.push_cmd(Cmd::Goto(bb_label(bb)));
        }
    }

    pub fn shim_with(&mut self, def_id: DefId, args: &[Operand<'tcx>], fname: String) -> String {
        // We only shim core

        if !self.is_core(def_id.krate) {
            return fname;
        }

        let name = with_no_trimmed_paths!(self.tcx.def_path_str(def_id));

        log::debug!("Can I shim: {name}");

        match name.as_str() {
            // slice::len
            "core::slice::<impl [T]>::len" => runtime::slice::SLICE_LEN.to_string(),
            "core::ptr::const_ptr::<impl *const T>::add"
            | "core::ptr::const_ptr::<impl *const T>::offset" => {
                log::debug!("adding PtrPlus<{:#?}>", self.operand_ty(&args[0]));
                self.global_env.add_runtime(CustomRuntime::PtrPlus(
                    self.operand_ty(&args[0]),
                    fname.clone(),
                ));
                fname
            }
            "core::ptr::slice_from_raw_parts" => runtime::ptr::SLICE_FROM_RAW_PARTS.to_string(),
            _ => {
                if !def_id.is_local() {
                    log::warn!("Non-local function is not shimed: {:#?}", name)
                };
                fname
            }
        }
    }
}
