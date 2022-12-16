use crate::{config::ExecMode, prelude::*};
use rustc_middle::mir::pretty::write_mir_fn;
use rustc_middle::ty::ParamTy;

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn push_alloc_local_decls(&mut self, mir: &Body<'tcx>) {
        mir.local_decls().iter_enumerated().for_each(|(loc, decl)| {
            if self.local_is_in_store(loc) {
                return;
            }
            if let TyKind::Never = decl.ty.kind() {
                return;
            }
            match mir.local_kind(loc) {
                LocalKind::Arg => {
                    let temp = self.temp_var();
                    self.push_cmd(Cmd::Assignment {
                        variable: temp.clone(),
                        assigned_expr: Expr::PVar(self.name_from_local(loc)),
                    });
                    self.push_alloc_into_local(loc, decl.ty);
                    self.push_place_write(loc.into(), Expr::PVar(temp), decl.ty)
                }
                _ => self.push_alloc_into_local(loc, decl.ty),
            }
        });
    }

    fn push_free_local_decls_and_return(&mut self, mir: &Body<'tcx>) {
        self.push_label(names::ret_label());
        mir.local_decls().iter_enumerated().for_each(|(loc, decl)| {
            if self.local_is_in_store(loc) {
                return;
            }
            if let TyKind::Never = decl.ty.kind() {
                return;
            }
            self.push_free_local(loc, decl.ty);
        });
        self.push_cmd(Cmd::ReturnNormal);
    }

    pub fn log_body(&self) {
        use std::io::*;
        let mut buf = BufWriter::new(Vec::new());
        write_mir_fn(self.tcx, self.mir(), &mut |_, _| Ok(()), &mut buf).unwrap();
        let bytes = buf.into_inner().unwrap();
        let string = String::from_utf8(bytes).unwrap();
        log::debug!("{}", string)
    }

    fn gather_type_params(&self) -> Vec<String> {
        let mir = self.mir();
        // FIXME: Is it right to skip the binder? I think no, this might lead to issues in trait impls.

        let mut all_param_tys: Vec<_> = mir
            .args_iter()
            .map(|local| mir.local_decls()[local].ty)
            .chain(std::iter::once(mir.return_ty()))
            .filter_map(|x: Ty<'tcx>| {
                if let TyKind::Param(ParamTy { index, name }) = x.kind() {
                    Some((index, name))
                } else {
                    None
                }
            })
            .collect();
        log::debug!("{:?}", &all_param_tys);
        all_param_tys.sort_unstable_by_key(|x| x.0);
        all_param_tys.dedup_by_key(|x| x.0);
        all_param_tys
            .into_iter()
            .map(|x| Self::param_type_name(*x.0, *x.1))
            .collect()
    }

    pub fn push_body(mut self) -> Proc {
        let mir_body = self.mir();
        let proc_name =
            rustc_middle::ty::print::with_no_trimmed_paths!(self.tcx.def_path_str(self.body_did()));

        log::debug!("Compiling {}", proc_name);
        // If body_ctx is mutable, we might as well add currently compiled gil body to it and create only one vector
        // We can then shrink it to size when needed.
        // log::debug!("{} : {:#?}", proc_name, mir_body);
        self.log_body();
        if mir_body.is_polymorphic && self.config.mode != ExecMode::Verification {
            fatal!(self, "Polymorphism is not handled outside of verification.")
        }
        if mir_body.generator_kind().is_some() {
            fatal!(self, "Generators are not handled yet.")
        }

        let args: Vec<String> = self
            .gather_type_params()
            .into_iter()
            .chain(
                mir_body
                    .args_iter()
                    .map(|local| self.name_from_local(local)),
            )
            .collect();
        self.push_alloc_local_decls(mir_body);
        for (bb, bb_data) in mir_body.basic_blocks.iter_enumerated() {
            if !bb_data.is_cleanup {
                self.push_basic_block(bb, bb_data);
            }
        }
        self.push_free_local_decls_and_return(mir_body);
        self.make_proc(proc_name, args)
    }
}
