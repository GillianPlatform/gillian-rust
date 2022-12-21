use crate::prelude::*;
use rustc_middle::ty::GenericParamDefKind;

pub trait HasGenericArguments<'tcx>: HasDefId + HasTyCtxt<'tcx> {
    fn generic_types(&self) -> Vec<(u32, Symbol)> {
        let mut tys = vec![];
        let mut did_opt = Some(self.did());
        while let Some(did) = did_opt {
            let generics = self.tcx().generics_of(did);
            for param in &generics.params {
                match param.kind {
                    GenericParamDefKind::Type { .. } => tys.push((param.index, param.name)),
                    GenericParamDefKind::Lifetime => (),
                    GenericParamDefKind::Const { .. } => {
                        fatal!(self, "{:?} has const generics", did)
                    }
                }
            }
            did_opt = generics.parent;
        }
        tys.sort_by_key(|x| x.0);
        tys.dedup_by_key(|x| x.0);
        tys
    }
}
