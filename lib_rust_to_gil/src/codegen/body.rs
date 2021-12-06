use crate::prelude::*;

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn push_alloc_local_decls(&mut self, mir: &Body<'tcx>) {
        mir.local_decls().iter_enumerated().for_each(|(loc, decl)| {
            match (mir.local_kind(loc), self.place_is_in_memory(&loc.into())) {
                (LocalKind::Arg, true) => {
                    let temp = self.temp_var();
                    self.push_cmd(Cmd::Assignment {
                        variable: temp.clone(),
                        assigned_expr: Expr::PVar(self.name_from_local(&loc)),
                    });
                    self.push_alloc_into_local(loc, decl.ty);
                    self.push_place_write(&loc.into(), Expr::PVar(temp), decl.ty)
                }
                (LocalKind::Arg, false) => (),
                (_, true) => {
                    self.push_alloc_into_local(loc, decl.ty);
                }
                (_, false) => {
                    let uninitialized = self.type_in_store_encoding(decl.ty).uninitialized();
                    self.push_cmd(Cmd::Assignment {
                        variable: self.name_from_local(&loc),
                        assigned_expr: Expr::Lit(uninitialized),
                    })
                }
            }
        });
    }

    fn push_free_local_decls_and_return(&mut self, mir: &Body<'tcx>) {
        self.push_label(names::ret_label());
        mir.local_decls().iter_enumerated().for_each(|(loc, decl)| {
            if let LocalKind::Arg = mir.local_kind(loc) {
                // Don't bind arguments, they're already bound
                return;
            };
            if self.place_is_in_memory(&loc.into()) {
                self.push_free_local(loc, decl.ty);
            }
        });
        self.push_cmd(Cmd::ReturnNormal);
    }

    // pub fn push_free_local_decls(&mut self, mir: &Body<'tcx>) {
    //     mir.local_decls().iter_enumerated().for_each(|(loc, decl)) {
    //         if let LocalKind::Arg = mir.local_kind(loc) {
    //             // Don't free the arguments
    //             return;
    //         };
    //     }
    // }

    fn push_global_env_call(&mut self) {
        let call = Cmd::Call {
            variable: names::unused_var(),
            proc_ident: Expr::string(names::global_env_proc()),
            parameters: vec![],
            error_lab: None,
            bindings: None,
        };
        self.push_cmd(call)
    }

    pub fn push_body(mut self) -> Proc {
        let mir_body = self.mir();
        let proc_name = self.ty_ctxt.item_name(self.instance.def_id());

        log::debug!("Compiling {}", proc_name);
        // If body_ctx is mutable, we might as well add currently compiled gil body to it and create only one vector
        // We can then shrink it to size when needed.
        // log::debug!("{} : {:#?}", proc_name, mir_body);
        if mir_body.is_polymorphic {
            fatal!(self, "Polymorphism is not handled yet.")
        }
        if mir_body.generator_kind().is_some() {
            fatal!(self, "Generators are not handled yet.")
        }
        if proc_name.to_string() == "main" {
            self.push_global_env_call();
        }
        let args: Vec<String> = mir_body
            .args_iter()
            .map(|local| self.sanitized_original_name_from_local(&local).unwrap())
            .collect();
        self.push_alloc_local_decls(mir_body);
        for (bb, bb_data) in mir_body.basic_blocks().iter_enumerated() {
            self.push_basic_block(&bb, bb_data);
        }
        self.push_free_local_decls_and_return(mir_body);
        self.make_proc(proc_name.to_string(), args)
    }
}
