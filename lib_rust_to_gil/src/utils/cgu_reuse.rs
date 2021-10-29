use crate::prelude::*;
use rustc_codegen_ssa::{CompiledModule, ModuleKind};
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::mir::mono::CodegenUnit;
use rustc_session::cgu_reuse_tracker::CguReuse;

// Copied from the Cranelift backend
// Adapted from https://github.com/rust-lang/rust/blob/303d8aff6092709edd4dbd35b1c88e9aa40bf6d8/src/librustc_codegen_ssa/base.rs#L922-L953
pub fn determine_cgu_reuse<'tcx>(tcx: TyCtxt<'tcx>, cgu: &CodegenUnit<'tcx>) -> CguReuse {
    if !tcx.dep_graph.is_fully_enabled() {
        return CguReuse::No;
    }

    let work_product_id = &cgu.work_product_id();
    if tcx
        .dep_graph
        .previous_work_product(work_product_id)
        .is_none()
    {
        // We don't have anything cached for this CGU. This can happen
        // if the CGU did not exist in the previous session.
        return CguReuse::No;
    }

    // Try to mark the CGU as green. If it we can do so, it means that nothing
    // affecting the LLVM module has changed and we can re-use a cached version.
    // If we compile with any kind of LTO, this means we can re-use the bitcode
    // of the Pre-LTO stage (possibly also the Post-LTO version but we'll only
    // know that later). If we are not doing LTO, there is only one optimized
    // version of each module, so we re-use that.
    let dep_node = cgu.codegen_dep_node(tcx);
    assert!(
        !tcx.dep_graph.dep_node_exists(&dep_node),
        "CompileCodegenUnit dep-node for CGU `{}` already exists before marking.",
        cgu.name()
    );

    if tcx.try_mark_green(&dep_node) {
        CguReuse::PreLto
    } else {
        CguReuse::No
    }
}

// Adapted from the Cranelift backend
pub fn reuse_workproduct_for_cgu(
    tcx: TyCtxt<'_>,
    cgu: &CodegenUnit<'_>,
    work_products: &mut FxHashMap<WorkProductId, WorkProduct>,
) -> CompiledModule {
    let mut object = None;
    let work_product = cgu.work_product(tcx);
    if let Some(saved_file) = &work_product.saved_file {
        let obj_out = tcx
            .output_filenames(())
            .temp_path_ext(&"gil", Some(&cgu.name().as_str()));
        object = Some(obj_out.clone());
        let source_file = rustc_incremental::in_incr_comp_dir_sess(&tcx.sess, &saved_file);
        if let Err(err) = rustc_fs_util::link_or_copy(&source_file, &obj_out) {
            tcx.sess.err(&format!(
                "unable to copy {} to {}: {}",
                source_file.display(),
                obj_out.display(),
                err
            ));
        }
    }

    work_products.insert(cgu.work_product_id(), work_product);

    CompiledModule {
        name: cgu.name().to_string(),
        kind: ModuleKind::Regular,
        object,
        dwarf_object: None,
        bytecode: None,
    }
}
