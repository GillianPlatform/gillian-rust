use crate::prelude::*;
use crate::signature::build_signature;
use crate::temp_gen::TempGenerator;
use crate::utils;
use rustc_hir::def::DefKind;
use rustc_middle::mir::pretty::write_mir_fn;

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn push_alloc_local_decls(&mut self, mir: &Body<'tcx>) {
        mir.local_decls().iter_enumerated().for_each(|(loc, decl)| {
            if mir.local_kind(loc) == LocalKind::Arg {
                self.push_cmd(Cmd::Assignment {
                    variable: self.name_from_local(loc),
                    assigned_expr: Expr::PVar(
                        self.original_name_from_local(loc)
                            .unwrap_or("__debug__".into()),
                    ),
                });
            };

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
        write_mir_fn(self.tcx(), self.mir(), &mut |_, _| Ok(()), &mut buf).unwrap();
        let bytes = buf.into_inner().unwrap();
        let string = String::from_utf8(bytes).unwrap();
        log::trace!("{}", string)
    }

    pub fn args(&mut self) -> Vec<String> {
        if let DefKind::AssocConst = self.tcx().def_kind(self.did()) {
            utils::polymorphism::generic_types(self.did(), self.tcx())
                .into_iter()
                .map(|x| crate::codegen::typ_encoding::type_param_name(x.0, x.1))
                .collect()
        } else {
            let args = GenericArgs::identity_for_item(self.tcx(), self.did());
            let mut temp_gen = TempGenerator::new();
            // The temp_gen will not be used.
            let sig = build_signature(self.global_env, self.did(), args, &mut temp_gen);

            sig.physical_args().map(|a| a.name().to_string()).collect()
        }
    }

    pub fn push_body(mut self) -> Proc {
        let mir_body = self.mir();
        let proc_name =
            rustc_middle::ty::print::with_no_trimmed_paths!(self.tcx().def_path_str(self.did()));

        log::trace!(
            "Compiling {}, defkind: {:?}",
            proc_name,
            self.tcx().def_kind(self.did())
        );
        // If body_ctx is mutable, we might as well add currently compiled gil body to it and create only one vector
        // We can then shrink it to size when needed.
        // log::debug!("{} : {:#?}", proc_name, mir_body);
        self.log_body();
        if mir_body.coroutine_kind().is_some() {
            fatal!(self, "Generators are not handled yet.")
        }

        let args: Vec<String> = self.args();
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
