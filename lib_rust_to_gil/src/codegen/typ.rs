use crate::prelude::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::ty::{ConstKind, ParamEnv, TypeFoldable};
use rustc_target::abi::Size;

impl<'tcx> GilCtxt<'tcx> {
    // Adapted from RMC under MIT/Apache license.
    pub fn _monomorphize<T>(&self, value: T) -> T
    where
        T: TypeFoldable<'tcx>,
    {
        // Instance is Some(..) only when current codegen unit is a function.
        self.instance.subst_mir_and_normalize_erasing_regions(
            self.ty_ctxt,
            ParamEnv::reveal_all(),
            value,
        )
    }

    pub fn is_zst(val: &ConstKind) -> bool {
        match val {
            ConstKind::Value(ConstValue::Scalar(Scalar::Int(sci))) => sci.size() == Size::ZERO,
            _ => false,
        }
    }
}
