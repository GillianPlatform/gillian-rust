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
    ArrayIndex(Expr, EncodedType, i128),
    SliceIndex(Expr, EncodedType), // The EncodedType is the type of elements in the slice
    Plus(ArithKind, Expr, EncodedType),
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
            Self::ArrayIndex(e, ty, sz) => vec!["i".into(), e, ty.into(), sz.into()].into(),
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
    /// Every place should be constructed through that, as it will take care of
    /// handling boxes correctly.
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
    pub fn push_read_gil_place_in_memory(
        &mut self,
        res: String,
        gil_place: GilPlace<'tcx>,
        typ: Ty<'tcx>,
        copy: bool,
    ) {
        let (location, projection, meta) = gil_place.into_loc_proj_meta();
        let action = match meta {
            Some(_) => fatal!(self, "Should not be reading a fat pointer directly!"),
            None => MemoryAction::LoadValue {
                location,
                projection,
                copy,
                typ,
            },
        };
        self.push_action(res, action);
    }

    fn push_deinit_gil_place_in_memory(&mut self, gil_place: GilPlace<'tcx>, typ: Ty<'tcx>) {
        let (location, projection, meta) = gil_place.into_loc_proj_meta();
        if meta.is_some() {
            fatal!(self, "Deinit a fat location");
        }
        let action = MemoryAction::Deinit {
            location,
            projection,
            typ,
        };
        let ret = names::unused_var();
        self.push_action(ret, action);
    }

    fn push_write_gil_place_in_memory(
        &mut self,
        gil_place: GilPlace<'tcx>,
        value: Expr,
        typ: Ty<'tcx>,
    ) {
        let (location, projection, meta) = gil_place.into_loc_proj_meta();
        let action = match meta {
            Some(_) => fatal!(self, "Should not be writing to a fat pointer directly!"),
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

    pub fn push_read_gil_place(
        &mut self,
        gil_place: GilPlace<'tcx>,
        read_ty: Ty<'tcx>,
        copy: bool,
    ) -> Expr {
        let ret = self.temp_var();
        self.push_read_gil_place_in_memory(ret.clone(), gil_place, read_ty, copy);
        Expr::PVar(ret)
    }

    pub fn push_get_gil_place(&mut self, place: Place<'tcx>) -> GilPlace<'tcx> {
        let mut cur_gil_place = GilPlace::base(
            Expr::PVar(self.name_from_local(place.local)),
            self.place_ty(place.local.into()).ty,
        );
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
                    let new_base = if curr_typ.ty.is_box() {
                        // Box is a special case, it can be dereferenced,
                        // and has theoretically the exact same representation as a pointer.
                        // However, it's "value" is a tree with many things,
                        // and we need to access the actual pointer
                        Expr::PVar(new_base).lnth(0).lnth(0).lnth(0)
                    } else if ty_utils::is_mut_ref(curr_typ.ty) && self.prophecies_enabled() {
                        Expr::PVar(new_base).lnth(0)
                    } else {
                        Expr::PVar(new_base)
                    };
                    cur_gil_place = GilPlace::base(new_base, next_typ.ty);
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
                    let expr = self.push_place_read(local.into(), true);
                    match curr_typ.ty.kind() {
                        TyKind::Slice(ty) => cur_gil_place
                            .proj
                            .push(GilProj::SliceIndex(expr, self.encode_type(*ty))),
                        TyKind::Array(ty, cst) => cur_gil_place.proj.push(GilProj::ArrayIndex(
                            expr,
                            self.encode_type(*ty),
                            self.array_size_value(cst),
                        )),
                        _ => panic!("Indexing something that is neither an array nor a slice"),
                    }
                }
                // Ignored because I now have VField aggregating things.
                ProjectionElem::Downcast(_, _) => (),
                _ => fatal!(self, "Invalid projection element: {:#?}", proj),
            }
        }
        cur_gil_place
    }

    pub fn push_place_read(&mut self, place: Place<'tcx>, copy: bool) -> Expr {
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
                    let from = Expr::PVar(variable);
                    let v = self.temp_var();
                    self.push_cmd(Cmd::Assignment {
                        variable: v.clone(),
                        assigned_expr: from,
                    }); // FIXME:
                        // self.push_cmd(Cmd::Assignment {
                        //     variable,
                        //     assigned_expr: Expr::Lit(Literal::Nono),
                        // });
                    Expr::PVar(v)
                }
            }
        }
    }

    pub fn push_place_read_into(&mut self, ret: String, place: Place<'tcx>, copy: bool) {
        let assigned_expr = self.push_place_read(place, copy);
        let assign = Cmd::Assignment {
            variable: ret,
            assigned_expr,
        };
        self.push_cmd(assign)
    }

    pub fn push_place_write(&mut self, place: Place<'tcx>, value: Expr, value_ty: Ty<'tcx>) {
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

    pub fn push_deinit_place(&mut self, place: Place<'tcx>) {
        match self.place_in_store(place) {
            None => {
                let ty = self.place_ty(place).ty;
                let gil_place = self.push_get_gil_place(place);
                self.push_deinit_gil_place_in_memory(gil_place, ty);
            }
            Some(variable) => self.push_cmd(Cmd::Assignment {
                variable,
                assigned_expr: Expr::undefined(),
            }),
        }
    }
}
