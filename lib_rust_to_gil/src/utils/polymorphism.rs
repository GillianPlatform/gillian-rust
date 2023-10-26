use crate::prelude::*;
use rustc_hir::def::DefKind;
use rustc_middle::ty::{BoundVariableKind, GenericParamDefKind, Generics};

fn fill_item(args: &mut Vec<(u32, Symbol)>, tcx: TyCtxt, defs: &Generics) {
    if let Some(def_id) = defs.parent {
        let parent_defs = tcx.generics_of(def_id);
        fill_item(args, tcx, parent_defs);
    }
    fill_single(args, defs)
}

fn fill_single(args: &mut Vec<(u32, Symbol)>, defs: &Generics) {
    args.reserve(defs.params.len());
    for param in &defs.params {
        if let GenericParamDefKind::Const { .. } = param.kind {
            panic!("Const Generics are not handled for now");
        }
        if let GenericParamDefKind::Lifetime = param.kind {
            continue;
        }
        args.push((param.index, param.name));
    }
}

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

pub trait HasGenericArguments<'tcx>: HasDefId + HasTyCtxt<'tcx> {
    // TODO: refactor all this, I should only go through it once.
    // Plus, I could just build a nice iterator.

    fn has_generic_lifetimes(&self) -> bool {
        if let DefKind::AnonConst | DefKind::InlineConst = self.tcx().def_kind(self.did()) {
            return false;
        }
        self.tcx()
            .fn_sig(self.did())
            .instantiate_identity()
            .bound_vars()
            .iter()
            .any(|bound_var_kind| matches!(bound_var_kind, BoundVariableKind::Region(..)))
            || crate::utils::attrs::get_pre_for_post(self.did(), self.tcx())
                .is_some_and(|did| (did, self.tcx()).has_generic_lifetimes())
            || has_lifetimes_generics(self.did(), self.tcx())
    }

    fn generic_types(&self) -> Vec<(u32, Symbol)> {
        let defs = self.tcx().generics_of(self.did());
        let mut vec = Vec::with_capacity(defs.count());
        fill_item(&mut vec, self.tcx(), defs);
        vec
    }
}

impl<'tcx> HasGenericArguments<'tcx> for (DefId, TyCtxt<'tcx>) {}
