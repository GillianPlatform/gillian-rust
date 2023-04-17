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

pub fn is_ty_param(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::Param(_))
}

pub fn is_mut_ref_of_param_ty(ty: Ty) -> bool {
    if let Some(inner_ty) = mut_ref_inner(ty) {
        is_ty_param(inner_ty)
    } else {
        false
    }
}
