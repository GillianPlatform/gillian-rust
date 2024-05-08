use crate::prelude::*;
use rustc_infer::{
    infer::TyCtxtInferExt,
    traits::{ImplSource, Obligation, ObligationCause, SelectionError::Unimplemented, TraitEngine},
};
use rustc_middle::ty::AliasTy;
use rustc_middle::ty::{AssocKind, GenericArgsRef, TraitRef};
use rustc_span::symbol::Ident;
use rustc_trait_selection::traits::{translate_args, SelectionContext, TraitEngineExt};

pub enum ResolvedImpl<'tcx> {
    Param,
    Impl(Instance<'tcx>),
}

impl<'tcx> ResolvedImpl<'tcx> {
    pub fn expect_impl(self, global_env: &GlobalEnv<'tcx>) -> Instance<'tcx> {
        match self {
            Self::Param => fatal!(global_env, "Expected existing implementation!"),
            Self::Impl(imp) => imp,
        }
    }
}

pub trait TraitSolver<'tcx> {
    // Returns Some if there is an implementation that was found (ImplSource::UserDefined or not a trait member),
    // and None if it's a parameter. (ImplSource::Param)
    fn resolve_candidate(&self, def_id: DefId, substs: GenericArgsRef<'tcx>) -> ResolvedImpl<'tcx>;

    // Returns None if the trait is unimplemented
    fn resolve_associated_type(&self, assoc_id: DefId, for_ty: Ty<'tcx>) -> Option<Ty<'tcx>>;
}

impl<'tcx, T: HasTyCtxt<'tcx>> TraitSolver<'tcx> for T {
    fn resolve_candidate(&self, def_id: DefId, substs: GenericArgsRef<'tcx>) -> ResolvedImpl<'tcx> {
        log::trace!(
            "Resolving candidate for {:?}",
            self.tcx().def_path_str_with_args(def_id, substs)
        );
        let tcx = self.tcx();
        match tcx.trait_of_item(def_id) {
            None => ResolvedImpl::Impl(Instance::new(def_id, substs)),
            Some(trait_id) => {
                log::trace!(
                    "Resolving candidate for trait {:?}",
                    self.tcx().def_path_str_with_args(trait_id, substs)
                );
                // FIXME:
                // The following is extremely disgusting and will be cleaned up and factored out as soon as possible.
                // But right now it works and I have priorities.
                let param_env = tcx.param_env(def_id);
                let assoc = tcx.associated_item(def_id);
                let trait_ref = TraitRef::from_method(tcx, trait_id, substs);
                // Not sure what's happening below for now...
                let infer_ctx = tcx.infer_ctxt().ignoring_regions().build();

                let mut select_ctx = SelectionContext::new(&infer_ctx);
                let cause = ObligationCause::dummy();
                let obligation = Obligation::new(self.tcx(), cause, param_env, trait_ref);
                let selection = match select_ctx.select(&obligation) {
                    Ok(Some(selection)) => selection,
                    Ok(None) => panic!("Ambiguous!"),
                    Err(Unimplemented) => fatal!(
                        self,
                        "Got unimplemented when resolving {:?}.\n\
                         Please check that you have enabled --prophecies if working with prophecies.",
                        self.tcx().def_path_str_with_args(def_id, substs)
                    ),
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
                                fatal!(
                                    self,
                                    "{:?} not found in {:?}",
                                    assoc,
                                    impl_data.impl_def_id
                                );
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
                    _ => fatal!(self, "unsupported param source!"),
                }
            }
        }
    }

    fn resolve_associated_type(&self, assoc_id: DefId, for_ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        let trait_id = self
            .tcx()
            .trait_of_item(assoc_id)
            .expect("Not an associated type!");
        let param_env = self.tcx().param_env(assoc_id);
        let t_subst = self.tcx().mk_args(&[for_ty.into()]);
        let trait_ref = TraitRef::from_method(self.tcx(), trait_id, t_subst);
        let infer_ctx = self.tcx().infer_ctxt().ignoring_regions().build();
        let mut select_ctx = SelectionContext::new(&infer_ctx);
        let cause = ObligationCause::dummy();
        let obligation = Obligation::new(self.tcx(), cause, param_env, trait_ref);
        let selection = match select_ctx.select(&obligation) {
            Ok(Some(selection)) => selection,
            Ok(None) => panic!("Ambiguous!"),
            Err(Unimplemented) => return None,
            Err(e) => panic!("Error: {:?}", e),
        };
        let mut fulfill_cx = <dyn TraitEngine<'tcx>>::new(&infer_ctx);
        let impl_source = selection.map(|predicate| {
            fulfill_cx.register_predicate_obligation(&infer_ctx, predicate);
        });
        let impl_source = infer_ctx.resolve_vars_if_possible(impl_source);
        // let impl_source = infer_ctx.tcx.erase_regions(impl_source);
        match impl_source {
            ImplSource::UserDefined(impl_data) => {
                // This entire code is a hack...
                let name_of_assoc = self.tcx().associated_item(assoc_id).name;
                let associated_ty = self
                    .tcx()
                    .associated_items(impl_data.impl_def_id)
                    .find_by_name_and_kind(
                        self.tcx(),
                        Ident::with_dummy_span(name_of_assoc),
                        AssocKind::Type,
                        impl_data.impl_def_id,
                    )
                    .expect("Couldn't find the RepresentationType");
                Some(
                    self.tcx()
                        .type_of(associated_ty.def_id)
                        .instantiate_identity(),
                )
            }
            ImplSource::Param(..) => Some(Ty::new_alias(
                self.tcx(),
                rustc_type_ir::AliasKind::Projection,
                AliasTy::new(self.tcx(), assoc_id, t_subst),
            )),
            _ => {
                fatal!(
                    self,
                    "Unhandled Implementation source {:?} when resolving associated type {:?} for {:?}.\n
                    If you are verifying only type safety, make sure --prophecies is disabled",
                    impl_source,
                    self.tcx().def_path_str(assoc_id),
                    for_ty
                );
            }
        }
    }
}
