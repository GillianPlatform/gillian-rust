use rustc_ast::{AttrItem, AttrKind};
use rustc_ast::{Lit, LitKind, MacArgs, MacArgsEq, StrStyle};
use rustc_middle::ty::TyCtxt;
use rustc_session::Attribute;
use rustc_span::{def_id::DefId, Symbol};

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

fn extract_string_arg(attr: &AttrItem) -> Symbol {
    if let MacArgs::Eq(
        _,
        MacArgsEq::Hir(Lit {
            kind: LitKind::Str(sym, StrStyle::Cooked),
            ..
        }),
    ) = attr.args
    {
        sym
    } else {
        panic!("Predicate ins attribute must be a string");
    }
}

pub(crate) fn get_pre_id(def_id: DefId, tcx: TyCtxt) -> Option<Symbol> {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "spec", "precondition"],
    )
    .map(extract_string_arg)
}

pub(crate) fn get_post_id(def_id: DefId, tcx: TyCtxt) -> Option<Symbol> {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "spec", "postcondition"],
    )
    .map(extract_string_arg)
}

pub(crate) fn is_abstract_predicate(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "decl", "abstract_predicate"],
    )
    .is_some()
}

pub(crate) fn is_predicate(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "decl", "predicate"],
    )
    .is_some()
}

pub(crate) fn is_precondition(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "decl", "precondition"],
    )
    .is_some()
}

pub(crate) fn is_postcondition(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "decl", "postcondition"],
    )
    .is_some()
}

pub(crate) fn is_logic(def_id: DefId, tcx: TyCtxt) -> bool {
    is_predicate(def_id, tcx)
        || is_abstract_predicate(def_id, tcx)
        || is_precondition(def_id, tcx)
        || is_postcondition(def_id, tcx)
}
