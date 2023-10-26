use gillian::gil::{Assertion, Expr, Formula};

use crate::codegen::typ_encoding::EncodedType;

mod pred_names {
    pub(crate) const VALUE: &str = "value";
    pub(crate) const UNINIT: &str = "uninit";
    pub(crate) const MANY_UNINITS: &str = "many_uninits";
    pub(crate) const LFT: &str = "lft";
    pub(crate) const OBSERVER: &str = "value_observer";
    pub(crate) const CONTROLLER: &str = "pcy_controller";
    pub(crate) const PCY_VALUE: &str = "pcy_value";
    pub(crate) const OBSERVATION: &str = "observation";
}

pub(crate) fn value(pointer: Expr, typ: EncodedType, pointee: Expr) -> Assertion {
    let loc = pointer.clone().lnth(0);
    let proj = pointer.lnth(1);
    Assertion::GA {
        name: pred_names::VALUE.to_string(),
        ins: vec![loc, proj, typ.into()],
        outs: vec![pointee],
    }
}

pub(crate) fn uninit(pointer: Expr, typ: EncodedType) -> Assertion {
    let loc = pointer.clone().lnth(0);
    let proj = pointer.lnth(1);
    Assertion::GA {
        name: pred_names::UNINIT.to_string(),
        ins: vec![loc, proj, typ.into()],
        outs: vec![],
    }
}

pub(crate) fn many_uninits(pointer: Expr, typ: EncodedType, size: Expr) -> Assertion {
    let loc = pointer.clone().lnth(0);
    let proj = pointer.lnth(1);
    Assertion::GA {
        name: pred_names::MANY_UNINITS.to_string(),
        ins: vec![loc, proj, typ.into(), size],
        outs: vec![],
    }
}

pub(crate) fn alive_lft(lft: Expr) -> Assertion {
    Assertion::GA {
        name: pred_names::LFT.to_string(),
        ins: vec![lft],
        outs: vec![Expr::bool(true)],
    }
}

pub(crate) fn observer(prophecy: Expr, typ: EncodedType, model: Expr) -> Assertion {
    let pcy_var = prophecy.clone().lnth(0);
    let proj = prophecy.lnth(1);
    Assertion::GA {
        name: pred_names::OBSERVER.to_string(),
        ins: vec![pcy_var, proj, typ.into()],
        outs: vec![model],
    }
}

pub(crate) fn controller(prophecy: Expr, typ: EncodedType, model: Expr) -> Assertion {
    let pcy_var = prophecy.clone().lnth(0);
    let proj = prophecy.lnth(1);
    Assertion::GA {
        name: pred_names::CONTROLLER.to_string(),
        ins: vec![pcy_var, proj, typ.into()],
        outs: vec![model],
    }
}

pub(crate) fn pcy_value(prophecy: Expr, ty: EncodedType, value: Expr) -> Assertion {
    let pcy_var = prophecy.clone().lnth(0);
    let proj = prophecy.lnth(1);
    Assertion::GA {
        name: pred_names::PCY_VALUE.to_string(),
        ins: vec![pcy_var, proj, ty.into()],
        outs: vec![value],
    }
}

pub(crate) fn observation(formula: Formula) -> Assertion {
    let lowered = formula.into_expr();
    Assertion::GA {
        name: pred_names::OBSERVATION.to_string(),
        ins: vec![lowered],
        outs: vec![],
    }
}
