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
    OwnPred,
    RefMutInner,
}

impl Stubs {
    pub(crate) fn symbol(&self, prophecies_enabled: bool) -> Symbol {
        match self {
            Self::PredDefs => Symbol::intern("gillian::pred::defs"),
            Self::AssertStar => Symbol::intern("gillian::asrt::star"),
            Self::AssertPure => Symbol::intern("gillian::asrt::pure"),
            Self::AssertObservation => Symbol::intern("gillian::asrt::observation"),
            Self::AssertEmp => Symbol::intern("gillian::asrt::emp"),
            Self::AssertPointsTo => Symbol::intern("gillian::asrt::points_to"),
            Self::FormulaEqual => Symbol::intern("gillian::formula::equal"),
            Self::FormulaLessEq => Symbol::intern("gillian::formula::less_eq"),
            Self::FormulaLess => Symbol::intern("gillian::formula::less"),
            Self::MutRefGetProphecy => Symbol::intern("gillian::mut_ref::get_prophecy"),
            Self::MutRefSetProphecy => Symbol::intern("gillian::mut_ref::set_prophecy"),
            Self::ProphecyGetValue => Symbol::intern("gillian::prophecy::get_value"),
            Self::ProphecyField(_field) => {
                panic!("Cannot get prophecy field without arity")
            }
            Self::ProphecyObserver => Symbol::intern("gillian::prophecy::observer"),
            Self::ProphecyController => Symbol::intern("gillian::prophecy::controller"),
            Self::SeqNil => Symbol::intern("gillian::seq::nil"),
            Self::SeqAppend => Symbol::intern("gillian::seq::append"),
            Self::SeqPrepend => Symbol::intern("gillian::seq::prepend"),
            Self::SeqConcat => Symbol::intern("gillian::seq::concat"),
            Self::SeqLen => Symbol::intern("gillian::seq::len"),
            Self::RefMutInner => Symbol::intern("gillian::pcy::ownable::ref_mut_inner"),
            Self::OwnPred => {
                if prophecies_enabled {
                    Symbol::intern("gillian::pcy::ownable::own")
                } else {
                    Symbol::intern("gillian::ownable::own")
                }
            }
        }
    }

    pub(crate) fn for_fn_def_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Self> {
        if let TyKind::FnDef(did, _) = ty.kind() {
            crate::utils::attrs::diagnostic_item_string(*did, tcx).and_then(|name| {
                match name.as_str() {
                    "gillian::pred::defs" => Some(Stubs::PredDefs),
                    "gillian::asrt::star" => Some(Stubs::AssertStar),
                    "gillian::asrt::pure" => Some(Stubs::AssertPure),
                    "gillian::asrt::observation" => Some(Stubs::AssertObservation),
                    "gillian::asrt::emp" => Some(Stubs::AssertEmp),
                    "gillian::asrt::points_to" => Some(Stubs::AssertPointsTo),
                    "gillian::formula::equal" => Some(Stubs::FormulaEqual),
                    "gillian::formula::less_eq" => Some(Stubs::FormulaLessEq),
                    "gillian::formula::less" => Some(Stubs::FormulaLess),
                    "gillian::mut_ref::get_prophecy" => Some(Stubs::MutRefGetProphecy),
                    "gillian::mut_ref::set_prophecy" => Some(Stubs::MutRefSetProphecy),
                    "gillian::prophecy::get_value" => Some(Stubs::ProphecyGetValue),
                    "gillian::prophecy::observer" => Some(Stubs::ProphecyObserver),
                    "gillian::prophecy::controller" => Some(Stubs::ProphecyController),
                    "gillian::seq::empty" | "gillian::seq::nil" => Some(Stubs::SeqNil),
                    "gillian::seq::append" => Some(Stubs::SeqAppend),
                    "gillian::seq::prepend" => Some(Stubs::SeqPrepend),
                    "gillian::seq::concat" => Some(Stubs::SeqConcat),
                    "gillian::seq::len" => Some(Stubs::SeqLen),
                    "gillian::ownable::own" | "gillian::pcy::ownable::own" => Some(Stubs::OwnPred),
                    "gillian::pcy::ownable::ref_mut_inner" => Some(Stubs::RefMutInner),
                    _ => {
                        if let Some(fields) = name.strip_prefix("gillian::prophecy::field::") {
                            let mut iter = fields.split("::");
                            iter.next(); // skip "arity"
                            let field = iter.next().unwrap().parse().unwrap();
                            Some(Stubs::ProphecyField(field))
                        } else {
                            None
                        }
                    }
                }
            })
        } else {
            None
        }
    }
}
