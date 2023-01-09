use crate::prelude::*;
use rustc_infer::{
    infer::{DefiningAnchor, TyCtxtInferExt},
    traits::{ImplSource, Obligation, ObligationCause, SelectionError::Unimplemented, TraitEngine},
};
use rustc_middle::ty::{Binder, SubstsRef, TraitRef};
use rustc_trait_selection::traits::{translate_substs, SelectionContext, TraitEngineExt};

use super::predicate::PredCtx;

impl<'tcx, 'genv> PredCtx<'tcx, 'genv> {
    pub fn resolve_candidate(
        &self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> (DefId, SubstsRef<'tcx>) {
        let tcx = self.tcx();
        match tcx.trait_of_item(def_id) {
            None => (def_id, substs),
            Some(trait_id) => {
                // FIXME:
                // The following is extremely disgusting and will be cleaned up and factored out as soon as possible.
                // But right now it works and I have priorities.
                let param_env = tcx.param_env(def_id);
                let assoc = tcx.associated_item(def_id);
                let trait_ref = Binder::dummy(TraitRef::from_method(tcx, trait_id, substs));
                // Not sure what's happening below for now...
                let infer_ctx = tcx
                    .infer_ctxt()
                    .ignoring_regions()
                    .with_opaque_type_inference(DefiningAnchor::Bubble)
                    .build();

                let mut select_ctx = SelectionContext::new(&infer_ctx);
                let cause = ObligationCause::dummy();
                let obligation =
                    Obligation::new(cause, param_env, trait_ref.to_poly_trait_predicate());
                let selection = match select_ctx.select(&obligation) {
                    Ok(Some(selection)) => selection,
                    Ok(None) => panic!("Ambiguous!"),
                    Err(Unimplemented) => panic!("Unimplemented!"),
                    Err(e) => panic!("Error: {:?}", e),
                };
                let mut fulfill_cx = <dyn TraitEngine<'tcx>>::new(infer_ctx.tcx);
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
                                panic!("{:?} not found in {:?}", assoc, impl_data.impl_def_id);
                            });
                        let infer_ctx = tcx.infer_ctxt().build();

                        let param_env = param_env.with_reveal_all_normalized(tcx);
                        let substs = substs.rebase_onto(tcx, trait_def_id, impl_data.substs);
                        let substs = translate_substs(
                            &infer_ctx,
                            param_env,
                            impl_data.impl_def_id,
                            substs,
                            leaf_def.defining_node,
                        );
                        let leaf_substs = infer_ctx.tcx.erase_regions(substs);
                        (leaf_def.item.def_id, leaf_substs)
                    }
                    _ => unimplemented!(),
                }
            }
        }
    }
}
