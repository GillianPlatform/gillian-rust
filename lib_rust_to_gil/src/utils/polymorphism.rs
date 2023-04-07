use crate::prelude::*;
use rustc_ast::{Lit, LitKind, MacArgs, MacArgsEq, StrStyle};
use rustc_middle::ty::GenericParamDefKind;

pub trait HasGenericArguments<'tcx>: HasDefId + HasTyCtxt<'tcx> {
    // TODO: refactor all this, I should only go through it once.
    // Plus, I could just build a nice iterator.

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

pub trait HasGenericLifetimes<'tcx>: HasDefId + HasTyCtxt<'tcx> {
    fn generic_lifetimes(&self) -> Vec<String> {
        if let Some(v) = crate::utils::attrs::diagnostic_item_string(self.did(), self.tcx()) {
            if let "gillian::ownable::ref_mut_inner::open"
            | "gillian::ownable::ref_mut_inner::close"
            | "gillian::ownable::ref_mut_inner" = v.as_str()
            {
                return vec!["a".to_string()];
            }
        };
        let attr = crate::utils::attrs::get_attr(
            self.tcx().get_attrs_unchecked(self.did()),
            &["gillian", "parameters", "lifetimes"],
        );
        match attr {
            None => vec![],
            Some(attr) => {
                if let MacArgs::Eq(
                    _,
                    MacArgsEq::Hir(Lit {
                        kind: LitKind::Str(sym, StrStyle::Cooked),
                        ..
                    }),
                ) = &attr.args
                {
                    let str = sym.as_str();
                    if str.is_empty() {
                        vec![]
                    } else {
                        str.split(',').map(|s| s.to_string()).collect()
                    }
                } else {
                    panic!("Ill-formed gillian::pred::lifetime_tokens attribute")
                }
            }
        }
    }
}

impl<'tcx> HasGenericLifetimes<'tcx> for (DefId, TyCtxt<'tcx>) {}
