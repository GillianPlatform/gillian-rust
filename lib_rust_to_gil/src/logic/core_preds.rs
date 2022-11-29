use gillian::gil::{Assertion, Expr};

use crate::codegen::typ_encoding::EncodedType;

mod pred_names {
    pub(crate) const VALUE: &str = "value";
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
