use super::store_encoding::TypeInStoreEncoding;
use crate::prelude::*;

impl<'tcx> GilCtxt<'tcx> {
    pub fn push_alloc_local_decls(&mut self, mir: &Body<'tcx>) {
        mir.local_decls().iter_enumerated().for_each(|(loc, decl)| {
            if let LocalKind::Arg = mir.local_kind(loc) {
                // Don't bind arguments, they're already bound
                return;
            };
            if self.place_is_in_memory(&loc.into()) {
                self.push_alloc_into_local(loc, decl.ty);
            } else {
                let uninitialized = TypeInStoreEncoding::new(decl.ty).uninitialized();
                self.push_cmd(Cmd::Assignment {
                    variable: self.name_from_local(&loc),
                    assigned_expr: Expr::Lit(uninitialized),
                })
            }
        });
    }

    // pub fn push_free_local_decls(&mut self, mir: &Body<'tcx>) {
    //     mir.local_decls().iter_enumerated().for_each(|(loc, decl)) {
    //         if let LocalKind::Arg = mir.local_kind(loc) {
    //             // Don't free the arguments
    //             return;
    //         };
    //     }
    // }

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
        let args: Vec<String> = mir_body
            .args_iter()
            .map(|local| self.sanitized_original_name_from_local(&local).unwrap())
            .collect();
        self.push_alloc_local_decls(mir_body);
        for (bb, bb_data) in mir_body.basic_blocks().iter_enumerated() {
            self.push_basic_block(&bb, bb_data);
        }
        self.make_proc(proc_name.to_string(), args)
    }
}
