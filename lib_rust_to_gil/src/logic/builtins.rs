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
    AssertPointsToSlice,
    AssertUninit,
    AssertManyUninits,
    AssertMaybeUninit,
    AssertManyMaybeUninits,
    FormulaEqual,
    FormulaNotEqual,
    FormulaLessEq,
    FormulaLess,
    FormulaAnd,
    FormulaOr,
    FormulaNeg,
    FormulaForall,
    FormulaImplication,
    MutRefGetProphecy,
    MutRefSetProphecy,
    ProphecyGetValue,
    ProphecyObserver,
    ProphecyController,
    SeqNil,
    SeqAppend,
    SeqPrepend,
    SeqConcat,
    SeqHead,
    SeqLast,
    SeqTail,
    SeqLen,
    SeqAt,
    SeqSub,
    SeqRepeat,
    // The following are actually part of gilogic and would disappear
    // as soon as we support cross-crate compilation.
    OwnPred,
    MutRefOwnPred,
    // OptionOwnPred,
    TupleOwnPred,
    RefMutInner,
    InstantiateLVars,
    Spec,
    ExtractLemma,
    ExprExists,
    ExprForall,
    ExprEq,
    ExprNe,
    ExprImpl,
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
                "gillian::asrt::points_to_slice" => Some(Self::AssertPointsToSlice),
                "gillian::asrt::uninit" => Some(Self::AssertUninit),
                "gillian::asrt::many_uninits" => Some(Self::AssertManyUninits),
                "gillian::asrt::maybe_uninit" => Some(Self::AssertMaybeUninit),
                "gillian::asrt::many_maybe_uninits" => Some(Self::AssertManyMaybeUninits),
                "gillian::formula::equal" => Some(Self::FormulaEqual),
                "gillian::formula::not_equal" => Some(Self::FormulaNotEqual),
                "gillian::formula::less_eq" => Some(Self::FormulaLessEq),
                "gillian::formula::less" => Some(Self::FormulaLess),
                "gillian::formula::neg" => Some(Self::FormulaNeg),
                "gillian::formula::and" => Some(Self::FormulaAnd),
                "gillian::formula::or" => Some(Self::FormulaOr),
                "gillian::formula::forall" => Some(Self::FormulaForall),
                "gillian::expr::exists" => Some(Self::ExprExists),
                "gillian::expr::forall" => Some(Self::ExprForall),
                "gillian::expr::eq" => Some(Self::ExprEq),
                "gillian::expr::ne" => Some(Self::ExprNe),
                "gillian::expr::implies" => Some(Self::ExprImpl),
                "gillian::formula::implication" => Some(Self::FormulaImplication),
                "gillian::mut_ref::get_prophecy" => Some(Self::MutRefGetProphecy),
                "gillian::mut_ref::set_prophecy" => Some(Self::MutRefSetProphecy),
                "gillian::prophecy::get_value" => Some(Self::ProphecyGetValue),
                "gillian::prophecy::observer" => Some(Self::ProphecyObserver),
                "gillian::prophecy::controller" => Some(Self::ProphecyController),
                "gillian::seq::empty" | "gillian::seq::nil" => Some(Self::SeqNil),
                "gillian::seq::append" => Some(Self::SeqAppend),
                "gillian::seq::prepend" => Some(Self::SeqPrepend),
                "gillian::seq::concat" => Some(Self::SeqConcat),
                "gillian::seq::head" | "gillian::seq::first" => Some(Self::SeqHead),
                "gillian::seq::last" => Some(Self::SeqLast),
                "gillian::seq::tail" => Some(Self::SeqTail),
                "gillian::seq::len" => Some(Self::SeqLen),
                "gillian::seq::at" => Some(Self::SeqAt),
                "gillian::seq::sub" => Some(Self::SeqSub),
                "gillian::seq::repeat" => Some(Self::SeqRepeat),
                "gillian::ownable::own" | "gillian::pcy::ownable::own" => Some(Self::OwnPred),
                "gillian::ownable::mut_ref_own" | "gillian::pcy::ownable::mut_ref_own" => {
                    Some(Self::MutRefOwnPred)
                }
                "gillian::ownable::tuple_own" | "gillian::pcy::ownable::tuple_own" => {
                    Some(Self::TupleOwnPred)
                }
                "gillian::pcy::ownable::ref_mut_inner" => Some(Self::RefMutInner),
                "gillian::asrt::instantiate_lvars" => Some(Self::InstantiateLVars),
                "gillian::asrt::spec" => Some(Self::Spec),
                "gillian::asrt::extract_lemma" => Some(Self::ExtractLemma),
                _ => None,
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
    UnfoldSomething,
    FoldSomething,
    Into,
}

impl FnStubs {
    pub(crate) fn of_def_id(def_id: DefId, tcx: TyCtxt) -> Option<Self> {
        let is_into = tcx
            .trait_of_item(def_id)
            .is_some_and(|trait_id| tcx.is_diagnostic_item(Symbol::intern("Into"), trait_id));

        if is_into {
            return Some(Self::Into);
        }

        crate::utils::attrs::diagnostic_item_string(def_id, tcx).and_then(|name| {
            match name.as_str() {
                // "gillian::prophecies::check_obs_sat" => Some(Self::CheckObsSat),
                x if x.len() >= 17 && &x[..17] == "gillian::unfold::" => {
                    Some(Self::UnfoldSomething)
                }
                x if x.len() >= 15 && &x[..15] == "gillian::fold::" => Some(Self::FoldSomething),
                _ => None,
            }
        })
    }
}
