use crate::prelude::*;
use rustc_hir::def::DefKind;
use rustc_middle::ty::{BoundVariableKind, GenericParamDef, GenericParamDefKind, Generics};

// fn fill_item(args: &mut Vec<(u32, Symbol)>, tcx: TyCtxt, defs: &Generics) {
//     if let Some(def_id) = defs.parent {
//         let parent_defs = tcx.generics_of(def_id);
//         fill_item(args, tcx, parent_defs);
//     }
//     fill_single(args, defs)
// }

// fn fill_single(args: &mut Vec<(u32, Symbol)>, defs: &Generics) {
//     args.reserve(defs.params.len());
//     for param in &defs.params {
//         if let GenericParamDefKind::Const { .. } = param.kind {
//             panic!("Const Generics are not handled for now");
//         }
//         if let GenericParamDefKind::Lifetime = param.kind {
//             continue;
//         }
//         args.push((param.index, param.name));
//     }
// }

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

fn fill_item<F: FnMut(&GenericParamDef)>(tcx: TyCtxt, defs: &Generics, f: &mut F) {
    if let Some(def_id) = defs.parent {
        let parent_defs = tcx.generics_of(def_id);
        fill_item(tcx, parent_defs, f);
    }
    fill_single(defs, f)
}

fn fill_single<F: FnMut(&GenericParamDef)>(defs: &Generics, f: &mut F) {
    for param in &defs.params {
        if let GenericParamDefKind::Const {
            is_host_effect: true,
            ..
        } = param.kind
        {
            continue;
        }
        f(param);
    }
}

pub fn generic_types(did: DefId, tcx: TyCtxt) -> Vec<(u32, Symbol)> {
    let defs = tcx.generics_of(did);
    let mut vec = Vec::with_capacity(defs.count());
    fill_item(tcx, defs, &mut |param| {
        if let GenericParamDefKind::Const { .. } = param.kind {
            panic!("Const Generics are not handled for now");
        }
        if let GenericParamDefKind::Lifetime = param.kind {
            return;
        }

        vec.push((param.index, param.name))
    });
    vec
}

pub trait HasGenericArguments<'tcx>: HasDefId + HasTyCtxt<'tcx> {
    // TODO: refactor all this, I should only go through it once.
    // Plus, I could just build a nice iterator.
    #[deprecated]
    fn generic_types(&self) -> Vec<(u32, Symbol)> {
        generic_types(self.did(), self.tcx())
    }
}

impl<'tcx> HasGenericArguments<'tcx> for (DefId, TyCtxt<'tcx>) {}
