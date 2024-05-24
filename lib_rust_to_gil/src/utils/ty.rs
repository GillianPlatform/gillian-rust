use rustc_middle::ty::{ParamEnv, ParamTy};
use rustc_type_ir::TyKind;

use crate::prelude::*;

pub fn is_mut_ref(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::Ref(_, _, Mutability::Mut))
}

pub fn mut_ref_inner(ty: Ty) -> Option<Ty> {
    if let TyKind::Ref(_, ty, Mutability::Mut) = ty.kind() {
        Some(*ty)
    } else {
        None
    }
}

pub fn is_unsigned_integral(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::Uint(_))
}

pub fn is_ty_param(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::Param(_))
}

pub fn extract_param_ty(ty: Ty) -> ParamTy {
    match *ty.kind() {
        TyKind::Param(pty) => pty,
        _ => panic!("unexpected ParamTy"),
    }
}

pub fn is_mut_ref_of_param_ty(ty: Ty) -> bool {
    if let Some(inner_ty) = mut_ref_inner(ty) {
        is_ty_param(inner_ty)
    } else {
        false
    }
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
        if let "core::ptr::NonNull" | "std::ptr::NonNull" = tcx.def_path_str(adt_def.did()).as_str()
        {
            return true;
        }
    }
    false
}

pub fn is_seq<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    ty.ty_adt_def().is_some_and(|def| {
        tcx.get_diagnostic_item(Symbol::intern("gillian::seq")) == Some(def.did())
    })
}

pub fn is_unique<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    if let Some(adt_def) = ty.ty_adt_def() {
        if let "core::ptr::Unique" | "std::ptr::Unique" = tcx.def_path_str(adt_def.did()).as_str() {
            return true;
        }
    }
    false
}
