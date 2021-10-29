use crate::prelude::*;

impl<'tcx> BodyCtxt<'tcx> {
    pub fn compile_body(&mut self) -> Proc {
        let mir_body = self.mir();
        let proc_name = self.ty_ctxt.item_name(self.instance.def_id());
        // If body_ctx is mutable, we might as well add currently compiled gil body to it and create only one vector
        // We can then shrink it to size when needed.
        // log::debug!("{} : {:#?}", proc_name, mir_body);
        if mir_body.is_polymorphic {
            panic!("Polymorphism is not handled yet.")
        }
        if mir_body.generator_kind().is_some() {
            panic!("Generators are not handled yet.")
        }

        let args: Vec<String> = mir_body
            .args_iter()
            .map(|local| self.original_name_from_local(&local).unwrap())
            .collect();
        let compiled_body: Vec<ProcBodyItem> = mir_body
            .basic_blocks()
            .iter_enumerated()
            .flat_map(|(bb, bb_data)| self.compile_basic_block(&bb, &bb_data))
            .collect();
        Proc::new(proc_name.to_string(), args, compiled_body)
    }
}
