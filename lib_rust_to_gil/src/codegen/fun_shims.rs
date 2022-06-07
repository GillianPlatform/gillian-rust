use crate::codegen::place::{ArithKind, GilProj};
use crate::prelude::*;
use names::bb_label;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_hir::definitions::{DefPathData, DisambiguatedDefPathData};
use rustc_middle::ty::{Const, TypeAndMut};
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
            self.encode_type(ty),
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

macro_rules! d {
    ($p: pat) => {
        DisambiguatedDefPathData { data: $p, .. }
    };
}

macro_rules! tns {
    ($p: pat) => {
        d!(TypeNs($p))
    };
}

macro_rules! vns {
    ($p: pat) => {
        d!(ValueNs($p))
    };
}
impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn is_core(&self, krate: CrateNum) -> bool {
        matches!(self.tcx.crate_name(krate), sym::core)
    }

    pub fn push_function_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: &Option<(Place<'tcx>, BasicBlock)>,
    ) {
        // TODO: Handle cleanups at some point
        let (def_id, substs) = match func {
            Operand::Constant(box mir::Constant {
                literal: ConstantKind::Ty(Const { ty, val, .. }),
                ..
            }) if Self::const_is_zst(val) && ty.is_fn() => match ty.kind() {
                TyKind::FnDef(did, subst) => (*did, subst),
                tyk => fatal!(self, "unhandled TyKind for function name: {:#?}", tyk),
            },
            _ => fatal!(
                self,
                "Can't handle dynamic calls yet! Got fun operand: {:#?}",
                func
            ),
        };

        let fname = self.tcx.def_path_str_with_substs(def_id, *substs);
        if self.is_core(def_id.krate) {}
        let mut gil_args = Vec::with_capacity(args.len());
        for arg in args {
            gil_args.push(self.push_encode_operand(arg));
        }
        let fname = self.shim_with(def_id, args, fname).into();
        match destination {
            Some((place, bb)) => {
                let target = self.temp_var();
                self.push_cmd(Cmd::Call {
                    variable: target.clone(),
                    parameters: gil_args,
                    proc_ident: fname,
                    error_lab: None,
                    bindings: None,
                });
                let call_ret_ty = self.place_ty(place).ty;
                self.push_place_write(place, Expr::PVar(target), call_ret_ty);
                self.push_cmd(Cmd::Goto(bb_label(bb)));
            }
            None => {
                let variable = names::unused_var();
                self.push_cmd(Cmd::Call {
                    variable,
                    parameters: gil_args,
                    proc_ident: fname,
                    error_lab: None,
                    bindings: None,
                })
            }
        }
    }

    pub fn shim_with(&mut self, def_id: DefId, args: &[Operand<'tcx>], fname: String) -> String {
        // We only shim core

        if !self.is_core(def_id.krate) {
            return fname;
        }

        let path = self.tcx.def_path(def_id);

        use DefPathData::*;

        // Slice shims

        match path.data[..] {
            // slice::len
            [tns!(sym::slice), d!(Impl), vns!(sym::len)] => runtime::slice::SLICE_LEN.to_string(),

            // const_ptr::offset or const_ptr::add
            [tns!(sm), tns!(sym::const_ptr), d!(Impl), vns!(sym::add)]
            | [tns!(sm), tns!(sym::const_ptr), d!(Impl), vns!(sym::offset)]
                if sm.as_str() == "ptr" =>
            {
                log::debug!("adding PtrPlus<{:#?}>", self.operand_ty(&args[0]));
                self.global_env.add_runtime(CustomRuntime::PtrPlus(
                    self.operand_ty(&args[0]),
                    fname.clone(),
                ));
                fname
            }
            [_, vns!(sm)] if sm.as_str() == "slice_from_raw_parts" => {
                runtime::ptr::SLICE_FROM_RAW_PARTS.to_string()
            }
            _ => {
                if !def_id.is_local() {
                    log::warn!("Non-local function is not shimed: {:#?}", path)
                };
                fname
            }
        }
    }
}
