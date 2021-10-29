use crate::prelude::*;
use rustc_codegen_ssa::{CompiledModule, ModuleKind};
use rustc_data_structures::stable_hasher::{HashStable, StableHasher};
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};

pub struct ModuleCodegenResult(pub CompiledModule, pub Option<(WorkProductId, WorkProduct)>);

impl<HCX> HashStable<HCX> for ModuleCodegenResult {
    fn hash_stable(&self, _: &mut HCX, _: &mut StableHasher) {
        // do nothing
    }
}

pub fn emit_module(
    tcx: TyCtxt<'_>,
    name: String,
    kind: ModuleKind,
    module: Prog,
) -> ModuleCodegenResult {
    let tmp_file = tcx.output_filenames(()).temp_path_ext(&"gil", Some(&name));
    log::debug!("Writing to {:#?}", &tmp_file);
    if let Err(err) = std::fs::write(&tmp_file, format!("{}", module)) {
        tcx.sess.fatal(&format!("Error writing GIL file: {}", err));
    }

    let work_product = rustc_incremental::copy_cgu_workproduct_to_incr_comp_cache_dir(
        tcx.sess,
        &name,
        &Some(tmp_file.clone()),
    );

    ModuleCodegenResult(
        CompiledModule {
            name,
            kind,
            object: Some(tmp_file),
            dwarf_object: None,
            bytecode: None,
        },
        work_product,
    )
}
