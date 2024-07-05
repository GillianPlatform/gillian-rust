use num_bigint::BigInt;
use rustc_middle::ty::{self, ParamEnv};
use rustc_type_ir::TyKind;

use crate::prelude::*;

pub fn is_mut_ref(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::Ref(_, _, Mutability::Mut))
}

pub fn peel_mut_ref(ty: Ty) -> Option<Ty> {
    if let TyKind::Ref(_, ty, Mutability::Mut) = ty.kind() {
        Some(*ty)
    } else {
        None
    }
}

pub fn peel_any_ptr(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => Some(*ty),
        _ => None,
    }
}

pub fn is_unsigned_integral(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::Uint(_))
}

pub fn is_zst<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    tcx.layout_of(ParamEnv::reveal_all().and(tcx.erase_regions(ty)))
        .unwrap()
        .is_zst()
}

pub fn is_ref_of_zst<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    matches!(ty.kind(), TyKind::Ref(_, ty, _) if is_zst(*ty, tcx))
}

pub fn is_nonnull<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    if let Some(adt_def) = ty.ty_adt_def() {
        tcx.is_diagnostic_item(Symbol::intern("NonNull"), adt_def.did())
    } else {
        false
    }
}

pub fn peel_nonnull<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Ty<'tcx>> {
    if let TyKind::Adt(adt_def, subst) = ty.kind() {
        if tcx.is_diagnostic_item(Symbol::intern("NonNull"), adt_def.did()) {
            Some(subst.type_at(0))
        } else {
            None
        }
    } else {
        None
    }
}

pub fn is_seq<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    ty.ty_adt_def().is_some_and(|def| {
        tcx.get_diagnostic_item(Symbol::intern("gillian::seq")) == Some(def.did())
    })
}

pub fn is_unique<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    if let Some(adt_def) = ty.ty_adt_def() {
        // Sadly, no diagnostic item for Unique
        if let "core::ptr::Unique" | "std::ptr::Unique" = tcx.def_path_str(adt_def.did()).as_str() {
            return true;
        }
    }
    false
}

pub fn peel_unique<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Ty<'tcx>> {
    if let TyKind::Adt(adt_def, subst) = ty.kind() {
        if let "core::ptr::Unique" | "std::ptr::Unique" = tcx.def_path_str(adt_def.did()).as_str() {
            Some(subst.type_at(0))
        } else {
            None
        }
    } else {
        None
    }
}

pub fn int_bounds<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> (BigInt, BigInt) {
    match ty.kind() {
        TyKind::Uint(uint) => (
            BigInt::from(0),
            BigInt::from(1) << (uint.bit_width().unwrap_or(64)),
        ),
        TyKind::Int(int) => {
            // For now we assume 64 bit for usize.
            let width = int.bit_width().unwrap_or(64);
            let lb = BigInt::from(1) << (width - 1);
            let hb = lb.clone() - 1;
            (-lb, hb)
        }
        _ => tcx
            .dcx()
            .fatal(format!("Invalid type for int_bounds: {:#?}", ty)),
    }
}
