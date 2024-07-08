use rustc_ast::AttrKind;
use rustc_ast::Attribute;
use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::DefId, Symbol};

pub(crate) fn get_attr<'a>(attrs: &'a [Attribute], path: &[&str]) -> Option<&'a Attribute> {
    attrs.iter().find_map(|attr| {
        let kind = match &attr.kind {
            AttrKind::DocComment(..) => {
                return None;
            }
            AttrKind::Normal(p) => &p.item,
        };

        if kind.path.segments.len() != path.len() {
            return None;
        }

        let matches = kind
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

pub fn diagnostic_item_string(def_id: DefId, tcx: TyCtxt) -> Option<String> {
    get_attr(tcx.get_attrs_unchecked(def_id), &["rustc_diagnostic_item"])
        .and_then(|x| x.value_str())
        .map(|x| x.to_string())
}

pub(crate) fn get_pre_for_post(def_id: DefId, tcx: TyCtxt) -> Option<DefId> {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "spec", "postcondition", "pre_id"],
    )
    .and_then(|x| {
        let id = x.value_str().unwrap();
        tcx.get_diagnostic_item(id)
    })
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

pub(crate) fn is_timeless(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["gillian", "timeless"]).is_some()
}

pub(crate) fn is_borrow(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["gillian", "borrow"]).is_some()
}

pub(crate) fn is_specification(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "decl", "specification"],
    )
    .is_some()
}

pub(crate) fn is_lemma(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "decl", "lemma"],
    )
    .is_some()
}

pub(crate) fn should_translate(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "no_translate"],
    )
    .is_none()
}

pub(crate) fn is_trusted(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["gillian", "trusted"]).is_some()
}

pub(crate) fn is_extract_lemma(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "decl", "extract_lemma"],
    )
    .is_some()
}

pub(crate) fn is_fold(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "predicate", "fold"],
    )
    .is_some()
}
pub(crate) fn is_unfold(def_id: DefId, tcx: TyCtxt) -> bool {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "predicate", "unfold"],
    )
    .is_some()
}

pub(crate) fn get_gillian_spec_name(def_id: DefId, tcx: TyCtxt) -> Option<Symbol> {
    get_attr(tcx.get_attrs_unchecked(def_id), &["gillian", "spec"])
        .and_then(|attr| attr.value_str())
}

pub(crate) fn get_gillian_extract_lemma_name(def_id: DefId, tcx: TyCtxt) -> Option<Symbol> {
    get_attr(
        tcx.get_attrs_unchecked(def_id),
        &["gillian", "extract_lemma"],
    )
    .and_then(|attr| attr.value_str())
}

pub(crate) fn is_logic(def_id: DefId, tcx: TyCtxt) -> bool {
    [
        is_predicate,
        is_abstract_predicate,
        is_extract_lemma,
        is_lemma,
        is_fold,
        is_unfold,
        is_specification,
    ]
    .iter()
    .any(|f| f(def_id, tcx))
}

pub(crate) fn parent_trusted(mut def_id: DefId, tcx: TyCtxt) -> bool {
    while tcx.def_kind(def_id) != DefKind::Mod {
        if is_trusted(def_id, tcx) {
            return true;
        };
        def_id = tcx.parent(def_id);
    }
    false
}
