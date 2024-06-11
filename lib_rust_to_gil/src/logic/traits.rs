use crate::prelude::*;
use rustc_infer::{
    infer::TyCtxtInferExt,
    traits::{ImplSource, Obligation, ObligationCause, SelectionError::Unimplemented, TraitEngine},
};
use rustc_middle::ty::ParamEnv;
use rustc_middle::ty::{GenericArgsRef, TraitRef};
use rustc_trait_selection::traits::{translate_args, SelectionContext, TraitEngineExt};

pub enum ResolvedImpl<'tcx> {
    Param,
    Impl(Instance<'tcx>),
}

pub fn resolve_candidate<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    substs: GenericArgsRef<'tcx>,
) -> ResolvedImpl<'tcx> {
    log::trace!(
        "Resolving candidate for {:?}",
        tcx.def_path_str_with_args(def_id, substs)
    );
    match tcx.trait_of_item(def_id) {
        None => ResolvedImpl::Impl(Instance::new(def_id, substs)),
        Some(trait_id) => {
            log::trace!(
                "Resolving candidate for trait {:?}",
                tcx.def_path_str_with_args(trait_id, substs)
            );
            let assoc = tcx.associated_item(def_id);
            let trait_ref = TraitRef::from_method(tcx, trait_id, substs);
            // Not sure what's happening below for now...
            let infer_ctx = tcx.infer_ctxt().ignoring_regions().build();

            let mut select_ctx = SelectionContext::new(&infer_ctx);
            let cause = ObligationCause::dummy();
            let obligation = Obligation::new(tcx, cause, param_env, trait_ref);
            let selection = match select_ctx.select(&obligation) {
                Ok(Some(selection)) => selection,
                Ok(None) => panic!("Ambiguous!"),
                Err(Unimplemented) => {
                    fatal2!(
                        tcx,
                        "Got unimplemented when resolving {:?}.\n\
                         Please check that you have enabled --prophecies if working with prophecies.",
                        tcx.def_path_str_with_args(def_id, substs)
                    )
                }
                Err(e) => panic!("Error: {:?}", e),
            };
            let mut fulfill_cx = <dyn TraitEngine<'tcx>>::new(&infer_ctx);
            let impl_source = selection.map(|predicate| {
                // debug!("fulfill_obligation: register_predicate_obligation {:?}", predicate);
                fulfill_cx.register_predicate_obligation(&infer_ctx, predicate);
            });
            let impl_source = infer_ctx.resolve_vars_if_possible(impl_source);
            let impl_source = infer_ctx.tcx.erase_regions(impl_source);
            match impl_source {
                ImplSource::UserDefined(impl_data) => {
                    let trait_def_id = tcx.trait_id_of_impl(impl_data.impl_def_id).unwrap();
                    let trait_def = tcx.trait_def(trait_def_id);
                    let leaf_def = trait_def
                        .ancestors(tcx, impl_data.impl_def_id)
                        .unwrap()
                        .leaf_def(tcx, assoc.def_id)
                        .unwrap_or_else(|| {
                            fatal2!(tcx, "{:?} not found in {:?}", assoc, impl_data.impl_def_id);
                        });
                    let infer_ctx = tcx.infer_ctxt().build();

                    let param_env = param_env.with_reveal_all_normalized(tcx);
                    let substs = substs.rebase_onto(tcx, trait_def_id, impl_data.args);
                    let substs = translate_args(
                        &infer_ctx,
                        param_env,
                        impl_data.impl_def_id,
                        substs,
                        leaf_def.defining_node,
                    );
                    ResolvedImpl::Impl(Instance::new(leaf_def.item.def_id, substs))
                }
                ImplSource::Param(..) => ResolvedImpl::Param,
                _ => fatal2!(tcx, "unsupported param source!"),
            }
        }
    }
}
