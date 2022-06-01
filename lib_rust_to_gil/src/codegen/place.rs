use super::memory::MemoryAction;
use crate::prelude::*;

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub enum ArithKind {
    Wrap,
    Overflow,
}

impl ArithKind {
    fn is_wrapping(&self) -> bool {
        match self {
            ArithKind::Wrap => true,
            ArithKind::Overflow => false,
        }
    }
}

#[derive(Clone, Debug)]
pub enum GilProj {
    Field(u32, EncodedType),
    VField(u32, EncodedType, u32),
    Downcast(u32, EncodedType),
    ArrayIndex(Expr, EncodedType, i128),
    SliceIndex(Expr, EncodedType), // The EncodedType is the type of elements in the slice
    Plus(ArithKind, Expr, EncodedType),
    Cast(EncodedType, EncodedType),
}

impl GilProj {
    pub fn into_expr(self) -> Expr {
        match self {
            Self::Field(u, ty) => vec!["f".into(), Expr::int(u as i128), ty.into()].into(),
            Self::VField(u, ty, idx) => vec![
                "vf".into(),
                Expr::int(u as i128),
                ty.into(),
                Expr::int(idx as i128),
            ]
            .into(),
            Self::Downcast(u, ty) => vec!["d".into(), Expr::int(u as i128), ty.into()].into(),
            Self::ArrayIndex(e, ty, sz) => vec!["i".into(), e, ty.into(), sz.into()].into(),
            Self::Cast(from_ty, into_ty) => vec!["c".into(), from_ty.into(), into_ty.into()].into(),
            Self::Plus(ak, e, ty) => vec!["+".into(), ak.is_wrapping().into(), e, ty.into()].into(),
            Self::SliceIndex(e, ty) => Self::Plus(ArithKind::Overflow, e, ty).into_expr(),
        }
    }
}

#[derive(Debug)]
pub struct GilPlace<'tcx> {
    pub base: Expr,
    pub base_ty: Ty<'tcx>,
    pub proj: Vec<GilProj>,
}

impl<'tcx> GilPlace<'tcx> {
    pub fn base(base: Expr, base_ty: Ty<'tcx>) -> GilPlace<'tcx> {
        GilPlace {
            base,
            base_ty,
            proj: vec![],
        }
    }

    pub fn base_is_slice(&self) -> bool {
        matches!(self.base_ty.kind(), TyKind::Slice(..))
    }

    pub fn into_loc_proj_meta(self) -> (Expr, Expr, Option<Expr>) {
        let (bloc, bproj, bmeta) = if self.base_is_slice() {
            let addr = Expr::lnth(self.base.clone(), 0);
            let meta = Expr::lnth(self.base, 1);
            let loc = Expr::lnth(addr.clone(), 0);
            let proj = Expr::lnth(addr, 1);
            (loc, proj, Some(meta))
        } else {
            let loc = Expr::lnth(self.base.clone(), 0);
            let proj = Expr::lnth(self.base, 1);
            (loc, proj, None)
        };
        if self.proj.is_empty() {
            (bloc, bproj, bmeta)
        } else {
            let new_proj: Vec<_> = self.proj.into_iter().map(GilProj::into_expr).collect();
            let full_proj = Expr::lst_concat(bproj, new_proj.into());
            (bloc, full_proj, None)
        }
    }

    pub fn into_expr_ptr(self) -> Expr {
        if self.proj.is_empty() {
            return self.base;
        }
        let (loc, total_proj, meta) = self.into_loc_proj_meta();
        match meta {
            None => vec![loc, total_proj].into(),
            Some(meta) => vec![vec![loc, total_proj].into(), meta].into(),
        }
    }
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    // Careful: array_ty.kind() should always be [element_ty; _]
    pub fn push_cast_array_to_element_pointer(
        &mut self,
        e: Expr,
        array_ty: Ty<'tcx>,
        element_ty: Ty<'tcx>,
    ) -> Expr {
        // Casting an array to the first element pointer is the same operation as getting the 0th element.
        let mut place = GilPlace::base(e, array_ty);
        place.proj.push(GilProj::Cast(
            self.encode_type(array_ty),
            self.encode_type(element_ty),
        ));
        place.into_expr_ptr()
    }

    fn push_read_gil_place_in_memory(
        &mut self,
        res: String,
        gil_place: GilPlace<'tcx>,
        typ: Ty<'tcx>,
        copy: bool,
    ) {
        let (location, projection, meta) = gil_place.into_loc_proj_meta();
        let action = match meta {
            Some(size) => MemoryAction::LoadSlice {
                location,
                projection,
                size,
                copy,
                typ,
            },
            None => MemoryAction::LoadValue {
                location,
                projection,
                copy,
                typ,
            },
        };
        self.push_action(res, action);
    }

    fn push_write_gil_place_in_memory(
        &mut self,
        gil_place: GilPlace<'tcx>,
        value: Expr,
        typ: Ty<'tcx>,
    ) {
        let (location, projection, meta) = gil_place.into_loc_proj_meta();
        let action = match meta {
            Some(size) => MemoryAction::StoreSlice {
                location,
                projection,
                size,
                typ,
                value,
            },
            None => MemoryAction::StoreValue {
                location,
                projection,
                typ,
                value,
            },
        };
        let ret = names::unused_var();
        self.push_action(ret, action);
    }

    fn push_read_gil_place(
        &mut self,
        gil_place: GilPlace<'tcx>,
        read_ty: Ty<'tcx>,
        copy: bool,
    ) -> Expr {
        let ret = self.temp_var();
        self.push_read_gil_place_in_memory(ret.clone(), gil_place, read_ty, copy);
        Expr::PVar(ret)
    }

    pub fn push_get_gil_place(&mut self, place: &Place<'tcx>) -> GilPlace<'tcx> {
        let mut cur_gil_place = GilPlace {
            base: Expr::PVar(self.name_from_local(&place.local)),
            proj: vec![],
            base_ty: self.place_ty(&place.local.into()).ty,
        };
        for (idx, proj) in place.projection.into_iter().enumerate() {
            let curr_typ = self.place_ty_until(place, idx);
            match proj {
                ProjectionElem::Deref => {
                    let new_base = self.temp_var();
                    self.push_read_gil_place_in_memory(
                        new_base.clone(),
                        cur_gil_place,
                        curr_typ.ty,
                        true,
                    );
                    let next_typ = self.place_ty_until(place, idx + 1);
                    cur_gil_place = GilPlace {
                        base: Expr::PVar(new_base),
                        proj: vec![],
                        base_ty: next_typ.ty,
                    };
                }
                ProjectionElem::Field(u, _) => match curr_typ.variant_index {
                    Some(vidx) => cur_gil_place.proj.push(GilProj::VField(
                        u.as_u32(),
                        self.encode_type(curr_typ.ty),
                        vidx.as_u32(),
                    )),
                    None => cur_gil_place
                        .proj
                        .push(GilProj::Field(u.as_u32(), self.encode_type(curr_typ.ty))),
                },

                ProjectionElem::Index(local) => {
                    let expr = self.push_place_read(&local.into(), true);
                    match curr_typ.ty.kind() {
                        TyKind::Slice(ty) => cur_gil_place
                            .proj
                            .push(GilProj::SliceIndex(expr, self.encode_type(ty))),
                        TyKind::Array(ty, cst) => cur_gil_place.proj.push(GilProj::ArrayIndex(
                            expr,
                            self.encode_type(ty),
                            self.array_size_value(cst),
                        )),
                        _ => panic!("Indexing something that is neither an array nor a slice"),
                    }
                }
                // Place pointer should contain their types? But so far, I think this has no effect.
                ProjectionElem::Downcast(_, u) => cur_gil_place
                    .proj
                    .push(GilProj::Downcast(u.as_u32(), self.encode_type(curr_typ.ty))),
                _ => fatal!(self, "Invalid projection element: {:#?}", proj),
            }
        }
        cur_gil_place
    }

    pub fn push_place_read(&mut self, place: &Place<'tcx>, copy: bool) -> Expr {
        match self.place_in_store(place) {
            None => {
                let read_ty = self.place_ty(place).ty;
                let gil_place = self.push_get_gil_place(place);
                self.push_read_gil_place(gil_place, read_ty, copy)
            }
            Some(variable) => {
                if copy {
                    Expr::PVar(variable)
                } else {
                    let from = Expr::PVar(variable.clone());
                    let v = self.temp_var();
                    self.push_cmd(Cmd::Assignment {
                        variable: v.clone(),
                        assigned_expr: from,
                    });
                    self.push_cmd(Cmd::Assignment {
                        variable,
                        assigned_expr: Expr::Lit(Literal::Nono),
                    });
                    Expr::PVar(v)
                }
            }
        }
    }

    pub fn push_place_read_into(&mut self, ret: String, place: &Place<'tcx>, copy: bool) {
        let assigned_expr = self.push_place_read(place, copy);
        let assign = Cmd::Assignment {
            variable: ret,
            assigned_expr,
        };
        self.push_cmd(assign)
    }

    pub fn push_place_write(&mut self, place: &Place<'tcx>, value: Expr, value_ty: Ty<'tcx>) {
        match self.place_in_store(place) {
            None => {
                let gil_place = self.push_get_gil_place(place);
                self.push_write_gil_place_in_memory(gil_place, value, value_ty);
            }
            Some(variable) => self.push_cmd(Cmd::Assignment {
                variable,
                assigned_expr: value,
            }),
        }
    }

    pub fn encode_simple_ptr_cast(
        &mut self,
        e: Expr,
        from_ty: Ty<'tcx>,
        into_ty: Ty<'tcx>,
    ) -> Expr {
        let mut gil_place = GilPlace::base(e, from_ty);
        gil_place.proj.push(GilProj::Cast(
            self.encode_type(from_ty),
            self.encode_type(into_ty),
        ));
        gil_place.into_expr_ptr()
    }
}
