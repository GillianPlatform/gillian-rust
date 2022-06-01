use crate::prelude::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::tcx::PlaceTy;
use rustc_middle::ty::{ConstKind, TypeFoldable};
use rustc_target::abi::Size;

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    // Adapted from RMC under MIT/Apache license.
    pub fn monomorphize<T>(&self, value: T) -> T
    where
        T: TypeFoldable<'tcx>,
    {
        // Instance is Some(..) only when current codegen unit is a function.
        // self.mir.subst_mir_and_normalize_erasing_regions(
        //     self.ty_ctxt,
        //     ParamEnv::reveal_all(),
        //     value,
        // )
        value
    }

    pub fn const_value_is_zst(val: &ConstValue) -> bool {
        match val {
            ConstValue::Scalar(Scalar::Int(sci)) => sci.size() == Size::ZERO,
            _ => false,
        }
    }

    pub fn const_is_zst(val: &ConstKind) -> bool {
        match val {
            ConstKind::Value(ConstValue::Scalar(Scalar::Int(sci))) => sci.size() == Size::ZERO,
            _ => false,
        }
    }

    pub fn operand_ty(&self, o: &Operand<'tcx>) -> Ty<'tcx> {
        self.monomorphize(o.ty(self.mir().local_decls(), self.tcx))
    }

    pub fn rvalue_ty(&self, rv: &Rvalue<'tcx>) -> Ty<'tcx> {
        self.monomorphize(rv.ty(self.mir().local_decls(), self.tcx))
    }

    pub fn place_ty(&self, place: &Place<'tcx>) -> PlaceTy<'tcx> {
        self.monomorphize(Place::ty_from(
            place.local,
            place.projection,
            self.mir().local_decls(),
            self.tcx,
        ))
    }

    pub fn place_ty_until(&self, place: &Place<'tcx>, i: usize) -> PlaceTy<'tcx> {
        let place_ty = Place::ty_from(
            place.local,
            &place.projection[..i],
            self.mir().local_decls(),
            self.tcx,
        );
        self.monomorphize(place_ty)
    }

    // pub fn field_def_type(&self, field_def: &FieldDef, subst: SubstsRef<'tcx>) -> Ty<'tcx> {
    //     self.monomorphize(field_def.ty(self.ty_ctxt, subst))
    // }

    // Gets the length of the tuple.
    // Panics if the type is not a Tuple
    // pub fn tuple_length(&self, ty: Ty<'tcx>) -> usize {
    //     let mut i = 0;
    //     ty.tuple_fields().for_each(|_| i += 1);
    //     i
    // }
}
