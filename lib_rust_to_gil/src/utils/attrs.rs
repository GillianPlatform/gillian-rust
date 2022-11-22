use rustc_ast::{AttrItem, AttrKind};
use rustc_middle::ty::TyCtxt;
use rustc_session::Attribute;
use rustc_span::def_id::DefId;

pub(crate) fn get_attr<'a>(attrs: &'a [Attribute], path: &[&str]) -> Option<&'a AttrItem> {
    attrs.iter().find_map(|attr| {
        let attr = match &attr.kind {
            AttrKind::DocComment(..) => {
                return None;
            }
            AttrKind::Normal(p) => &p.item,
        };

        if attr.path.segments.len() != path.len() {
            return None;
        }

        let matches = attr
            .path
            .segments
            .iter()
            .zip(path.iter())
            .fold(true, |acc, (seg, s)| acc && seg.ident.as_str() == *s);
        if matches {
            Some(attr)
        } else {
            None
        }
    })
}

pub(crate) fn is_abstract_predicate(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "decl", "abstract_predicate"],
    )
    .is_some()
}

pub(crate) fn is_predicate(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "decl", "predicate"],
    )
    .is_some()
}

pub(crate) fn is_logic(tcx: TyCtxt, def_id: DefId) -> bool {
    is_predicate(tcx, def_id) || is_abstract_predicate(tcx, def_id)
}
