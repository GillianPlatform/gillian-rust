use crate::prelude::*;
use rustc_ast::{AttrArgs, AttrArgsEq, LitKind, MetaItemLit, StrStyle};
use rustc_middle::ty::{GenericParamDefKind, Generics};

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
        if let GenericParamDefKind::Lifetime | GenericParamDefKind::Const { .. } = param.kind {
            panic!("I have consts or Lifetimes for some reason");
        }
        assert_eq!(param.index as usize, args.len(), "{args:#?}, {defs:#?}");
        args.push((param.index, param.name));
    }
}

pub trait HasGenericArguments<'tcx>: HasDefId + HasTyCtxt<'tcx> {
    // TODO: refactor all this, I should only go through it once.
    // Plus, I could just build a nice iterator.

    fn generic_types(&self) -> Vec<(u32, Symbol)> {
        let defs = self.tcx().generics_of(self.did());
        let mut vec = Vec::with_capacity(defs.count());
        fill_item(&mut vec, self.tcx(), defs);
        vec
    }
}

pub trait HasGenericLifetimes<'tcx>: HasDefId + HasTyCtxt<'tcx> {
    fn generic_lifetimes(&self) -> Vec<String> {
        if let Some(v) = crate::utils::attrs::diagnostic_item_string(self.did(), self.tcx()) {
            if let "gillian::ownable::own::open"
            | "gillian::ownable::own::close"
            | "gillian::pcy::ownable::ref_mut_inner"
            | "gillian::pcy::ownable::ref_mut_inner::close"
            | "gillian::pcy::ownable::ref_mut_inner::open" = v.as_str()
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
                if let AttrArgs::Eq(
                    _,
                    AttrArgsEq::Hir(MetaItemLit {
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
