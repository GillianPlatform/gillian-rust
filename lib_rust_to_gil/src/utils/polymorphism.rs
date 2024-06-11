use crate::prelude::*;
use rustc_hir::def::DefKind;
use rustc_middle::ty::{BoundVariableKind, GenericParamDefKind};

fn has_lifetimes_generics(did: DefId, tcx: TyCtxt) -> bool {
    let defs = tcx.generics_of(did);
    for param in &defs.params {
        if let GenericParamDefKind::Lifetime = param.kind {
            return true;
        }
    }
    defs.parent
        .is_some_and(|def_id| has_lifetimes_generics(def_id, tcx))
}

pub fn has_generic_lifetimes(did: DefId, tcx: TyCtxt) -> bool {
    let def_kind = tcx.def_kind(did);
    if let DefKind::AnonConst | DefKind::InlineConst | DefKind::Const | DefKind::AssocConst =
        def_kind
    {
        return false;
    }
    tcx.fn_sig(did)
        .instantiate_identity()
        .bound_vars()
        .iter()
        .any(|bound_var_kind| matches!(bound_var_kind, BoundVariableKind::Region(..)))
        || crate::utils::attrs::get_pre_for_post(did, tcx)
            .is_some_and(|did| has_generic_lifetimes(did, tcx))
        || has_lifetimes_generics(did, tcx)
}
