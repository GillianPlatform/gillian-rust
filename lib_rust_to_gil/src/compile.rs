use super::body_ctx::BodyCtxt;
use gillian::gil::*;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use std::vec::Vec;

// Here, we're talking a lot of inspiration from the semantics described by the MIR interpreter :
// https://doc.rust-lang.org/stable/nightly-rustc/src/rustc_mir/interpret/step.rs.html

pub struct ToGilTyCtxt<'gil, 'tcx>(&'gil TyCtxt<'tcx>);

impl<'gil, 'tcx> ToGilTyCtxt<'gil, 'tcx> {
    pub fn new(tcx: &'gil TyCtxt<'tcx>) -> Self {
        ToGilTyCtxt(tcx)
    }

    pub fn compile_body(&'gil self, key: &LocalDefId) -> Proc {
        let did = key.to_def_id();
        let proc_name = self.0.item_name(did);
        let mir_body = self.0.optimized_mir(did);
        let body_ctx = BodyCtxt::new(mir_body, &self.0);
        log::debug!("{} : {:#?}", proc_name, mir_body);
        if mir_body.is_polymorphic {
            panic!("Polymorphism is not handled yet.")
        }
        if mir_body.generator_kind().is_some() {
            panic!("Generators are not handled yet.")
        }

        // let ret_ptr = mir_body.local_decls.get(RETURN_PLACE);
        let args: Vec<String> = mir_body
            .args_iter()
            .map(|local| body_ctx.original_name_from_local(&local).unwrap())
            .collect();
        let compiled_body: Vec<ProcBodyItem> = mir_body
            .basic_blocks()
            .iter_enumerated()
            .flat_map(|(bb, bb_data)| body_ctx.compile_basic_block(&bb, &bb_data))
            .collect();
        Proc::new(proc_name.to_string(), args, compiled_body)
    }

    pub fn compile_prog(&'gil self) -> Prog {
        let procs: Vec<Proc> = self
            .0
            .mir_keys(())
            .iter()
            .map(|key| self.compile_body(key))
            .collect();
        for proc in procs {
            println!("{}", proc);
        }
        // let mir_main = self.0.optimized_mir(*key);
        // log::debug!("{:#?}", mir_main);
        // let gil_main = self.compile_function(mir_main);
        // log::debug!("{:#?}", gil_main);
        Prog::default()
    }
}
