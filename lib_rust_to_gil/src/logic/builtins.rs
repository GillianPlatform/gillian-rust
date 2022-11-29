use crate::prelude::*;

pub(crate) fn is_assertion_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    match ty.kind() {
        TyKind::Adt(adt, _) => {
            tcx.is_diagnostic_item(Symbol::intern("gillian::tys::assertion"), adt.did())
        }
        _ => false,
    }
}

pub(crate) fn is_formula_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    match ty.kind() {
        TyKind::Adt(adt, _) => {
            tcx.is_diagnostic_item(Symbol::intern("gillian::tys::formula"), adt.did())
        }
        _ => false,
    }
}

#[derive(PartialEq, Eq)]
pub(crate) enum Stubs {
    PredDefs,
    AssertStar,
    AssertPure,
    AssertEmp,
    AssertPointsTo,
    FormulaEqual,
    SeqNil,
    SeqAppend,
    SeqPrepend,
    SeqConcat,
    SeqLen,
}

pub(crate) fn get_stub<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Stubs> {
    if let TyKind::FnDef(did, _) = ty.kind() {
        let did = *did;
        if tcx.is_diagnostic_item(Symbol::intern("gillian::pred::defs"), did) {
            Some(Stubs::PredDefs)
        } else if tcx.is_diagnostic_item(Symbol::intern("gillian::asrt::star"), did) {
            Some(Stubs::AssertStar)
        } else if tcx.is_diagnostic_item(Symbol::intern("gillian::asrt::pure"), did) {
            Some(Stubs::AssertPure)
        } else if tcx.is_diagnostic_item(Symbol::intern("gillian::asrt::emp"), did) {
            Some(Stubs::AssertEmp)
        } else if tcx.is_diagnostic_item(Symbol::intern("gillian::asrt::points_to"), did) {
            Some(Stubs::AssertPointsTo)
        } else if tcx.is_diagnostic_item(Symbol::intern("gillian::formula::equal"), did) {
            Some(Stubs::FormulaEqual)
        } else if tcx.is_diagnostic_item(Symbol::intern("gillian::seq::nil"), did)
            || tcx.is_diagnostic_item(Symbol::intern("gillian::seq::empty"), did)
        {
            Some(Stubs::SeqNil)
        } else if tcx.is_diagnostic_item(Symbol::intern("gillian::seq::append"), did) {
            Some(Stubs::SeqAppend)
        } else if tcx.is_diagnostic_item(Symbol::intern("gillian::seq::prepend"), did) {
            Some(Stubs::SeqPrepend)
        } else if tcx.is_diagnostic_item(Symbol::intern("gillian::seq::concat"), did) {
            Some(Stubs::SeqConcat)
        } else if tcx.is_diagnostic_item(Symbol::intern("gillian::seq::len"), did) {
            Some(Stubs::SeqLen)
        } else {
            None
        }
    } else {
        None
    }
}
