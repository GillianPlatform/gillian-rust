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

#[derive(PartialEq, Eq, Debug)]
pub(crate) enum LogicStubs {
    PredDefs,
    AssertStar,
    AssertPure,
    AssertObservation,
    AssertEmp,
    AssertPointsTo,
    FormulaEqual,
    FormulaLessEq,
    FormulaLess,
    MutRefGetProphecy,
    MutRefSetProphecy,
    ProphecyGetValue,
    ProphecyField(u32),
    ProphecyObserver,
    ProphecyController,
    SeqNil,
    SeqAppend,
    SeqPrepend,
    SeqConcat,
    SeqLen,
    // The following are actually part of gilogic and would disappear
    // as soon as we support cross-crate compilation.
    OwnPred,
    MutRefOwnPred,
    OptionOwnPred,
    RefMutInner,
}

impl LogicStubs {
    pub(crate) fn of_def_id(def_id: DefId, tcx: TyCtxt) -> Option<Self> {
        crate::utils::attrs::diagnostic_item_string(def_id, tcx).and_then(|name| {
            match name.as_str() {
                "gillian::pred::defs" => Some(Self::PredDefs),
                "gillian::asrt::star" => Some(Self::AssertStar),
                "gillian::asrt::pure" => Some(Self::AssertPure),
                "gillian::asrt::observation" => Some(Self::AssertObservation),
                "gillian::asrt::emp" => Some(Self::AssertEmp),
                "gillian::asrt::points_to" => Some(Self::AssertPointsTo),
                "gillian::formula::equal" => Some(Self::FormulaEqual),
                "gillian::formula::less_eq" => Some(Self::FormulaLessEq),
                "gillian::formula::less" => Some(Self::FormulaLess),
                "gillian::mut_ref::get_prophecy" => Some(Self::MutRefGetProphecy),
                "gillian::mut_ref::set_prophecy" => Some(Self::MutRefSetProphecy),
                "gillian::prophecy::get_value" => Some(Self::ProphecyGetValue),
                "gillian::prophecy::observer" => Some(Self::ProphecyObserver),
                "gillian::prophecy::controller" => Some(Self::ProphecyController),
                "gillian::seq::empty" | "gillian::seq::nil" => Some(Self::SeqNil),
                "gillian::seq::append" => Some(Self::SeqAppend),
                "gillian::seq::prepend" => Some(Self::SeqPrepend),
                "gillian::seq::concat" => Some(Self::SeqConcat),
                "gillian::seq::len" => Some(Self::SeqLen),
                "gillian::ownable::own" | "gillian::pcy::ownable::own" => Some(Self::OwnPred),
                "gillian::ownable::mut_ref_own" | "gillian::pcy::ownable::mut_ref_own" => {
                    Some(Self::MutRefOwnPred)
                }
                "gillian::ownable::option_own" => Some(Self::OptionOwnPred),
                "gillian::pcy::ownable::ref_mut_inner" => Some(Self::RefMutInner),
                _ => {
                    if let Some(fields) = name.strip_prefix("gillian::prophecy::field::") {
                        let mut iter = fields.split("::");
                        iter.next(); // skip "arity"
                        let field = iter.next().unwrap().parse().unwrap();
                        Some(Self::ProphecyField(field))
                    } else {
                        None
                    }
                }
            }
        })
    }

    pub(crate) fn for_fn_def_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Self> {
        if let TyKind::FnDef(did, _) = ty.kind() {
            Self::of_def_id(*did, tcx)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub enum FnStubs {
    MutRefResolve,
    MutRefProphecyAutoUpdate,
    UnfoldSomething,
    FoldSomething,
}

impl FnStubs {
    pub(crate) fn of_def_id(def_id: DefId, tcx: TyCtxt) -> Option<Self> {
        crate::utils::attrs::diagnostic_item_string(def_id, tcx).and_then(|name| {
            match name.as_str() {
                "gillian::mut_ref::prophecy_auto_update" => Some(Self::MutRefProphecyAutoUpdate),
                "gillian::mut_ref::resolve" => Some(Self::MutRefResolve),
                x if x.len() >= 17 && &x[..17] == "gillian::unfold::" => {
                    Some(Self::UnfoldSomething)
                }
                x if x.len() >= 15 && &x[..15] == "gillian::fold::" => Some(Self::FoldSomething),
                _ => None,
            }
        })
    }
}
