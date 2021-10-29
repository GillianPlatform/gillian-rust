use crate::emit::{emit_module, ModuleCodegenResult};
use crate::prelude::*;
use core::any::Any;
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CodegenResults, CrateInfo, ModuleKind};

use rustc_errors::ErrorReported;
use rustc_metadata::EncodedMetadata;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::mir::mono::{CodegenUnit, MonoItem};
use rustc_middle::ty::TyCtxt;
use rustc_session::cgu_reuse_tracker::CguReuse;
use rustc_session::config::OutputFilenames;
use rustc_session::Session;

pub struct GilCodegenBackend();

impl GilCodegenBackend {
    pub fn new() -> Box<Self> {
        Box::new(GilCodegenBackend())
    }
}

fn codegen_cgu<'tcx>(tcx: TyCtxt<'tcx>, cgu_name: rustc_span::Symbol) -> ModuleCodegenResult {
    let cgu = tcx.codegen_unit(cgu_name);
    let items = cgu.items_in_deterministic_order(tcx);
    let mut prog = Prog::default();
    for (item, _) in items {
        match item {
            MonoItem::Fn(instance) => {
                let mut ctx = BodyCtxt::new(instance, tcx);
                let proc = ctx.compile_body();
                prog.add_proc(proc);
            }
            _ => panic!("MonoItem not handled yet: {:#?}", item),
        }
    }
    emit_module(
        tcx,
        cgu.name().as_str().to_string(),
        ModuleKind::Regular,
        prog,
    )
}

impl CodegenBackend for GilCodegenBackend {
    fn codegen_crate<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        _metadata: EncodedMetadata,
        _need_metadata_module: bool,
    ) -> Box<dyn Any> {
        tcx.sess.abort_if_errors();
        super::utils::init();

        let mut work_products = FxHashMap::<WorkProductId, WorkProduct>::default();

        let codegen_units: &'tcx [CodegenUnit<'_>] = if tcx.sess.opts.output_types.should_codegen()
        {
            tcx.collect_and_partition_mono_items(()).1
        } else {
            &[]
        };

        let compiled_modules = codegen_units
            .iter()
            .map(|cgu| {
                let cgu_reuse = crate::utils::determine_cgu_reuse(tcx, cgu);
                tcx.sess
                    .cgu_reuse_tracker
                    .set_actual_reuse(&cgu.name().as_str(), cgu_reuse);
                match cgu_reuse {
                    CguReuse::No => {}
                    CguReuse::PreLto => {
                        return crate::utils::reuse_workproduct_for_cgu(
                            tcx,
                            &*cgu,
                            &mut work_products,
                        );
                    }
                    CguReuse::PostLto => unreachable!(),
                }

                let dep_node = cgu.codegen_dep_node(tcx);
                let (ModuleCodegenResult(module, work_product), _) = tcx.dep_graph.with_task(
                    dep_node,
                    tcx,
                    cgu.name(),
                    codegen_cgu,
                    rustc_middle::dep_graph::hash_result,
                );

                if let Some((id, product)) = work_product {
                    work_products.insert(id, product);
                }
                module
            })
            .collect::<Vec<_>>();

        let target_cpu = tcx
            .sess
            .opts
            .cg
            .target_cpu
            .as_ref()
            .unwrap_or(&tcx.sess.target.cpu)
            .to_owned();

        Box::new((
            CodegenResults {
                modules: compiled_modules,
                allocator_module: None,
                metadata_module: None,
                metadata: EncodedMetadata::new(),
                crate_info: CrateInfo::new(tcx, target_cpu),
            },
            work_products,
        ))
    }

    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        _sess: &Session,
    ) -> Result<(CodegenResults, FxHashMap<WorkProductId, WorkProduct>), ErrorReported> {
        Ok(*ongoing_codegen
            .downcast::<(CodegenResults, FxHashMap<WorkProductId, WorkProduct>)>()
            .unwrap())
    }

    fn link(
        &self,
        _sess: &Session,
        _codegen_results: CodegenResults,
        _outputs: &OutputFilenames,
    ) -> Result<(), ErrorReported> {
        Ok(())
    }
}
