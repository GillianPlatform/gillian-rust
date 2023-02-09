use crate::prelude::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::tcx::PlaceTy;
use rustc_target::abi::Size;

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn const_value_is_zst(val: &ConstValue) -> bool {
        match val {
            ConstValue::Scalar(Scalar::Int(sci)) => sci.size() == Size::ZERO,
            _ => false,
        }
    }

    pub fn valtree_is_zst(val: &ValTree) -> bool {
        matches!(val, ValTree::Branch([]))
    }

    pub fn operand_ty(&self, o: &Operand<'tcx>) -> Ty<'tcx> {
        o.ty(self.mir().local_decls(), self.tcx)
    }

    pub fn rvalue_ty(&self, rv: &Rvalue<'tcx>) -> Ty<'tcx> {
        rv.ty(self.mir().local_decls(), self.tcx)
    }

    pub fn place_ty(&self, place: Place<'tcx>) -> PlaceTy<'tcx> {
        Place::ty_from(
            place.local,
            place.projection,
            self.mir().local_decls(),
            self.tcx,
        )
    }

    pub fn place_ty_until(&self, place: Place<'tcx>, i: usize) -> PlaceTy<'tcx> {
        Place::ty_from(
            place.local,
            &place.projection[..i],
            self.mir().local_decls(),
            self.tcx,
        )
    }
}
