use super::memory::MemoryAction;
use crate::prelude::*;

#[derive(Clone, Debug)]
pub enum GilProj {
    Field(u32),
    Downcast(u32),
    Index(Expr),
}

impl GilProj {
    pub fn into_expr(self) -> Expr {
        match self {
            Self::Field(u) => vec!["f".into(), Expr::int(u as i64)].into(),
            Self::Downcast(u) => vec!["d".into(), Expr::int(u as i64)].into(),
            Self::Index(e) => vec!["i".into(), e].into(),
        }
    }
}

pub struct GilPlace<'tcx> {
    pub base: String,
    pub base_ty: Ty<'tcx>,
    pub proj: Vec<GilProj>,
}

fn add_proj_thin(base: Expr, proj: Vec<Expr>) -> (Expr, Expr) {
    let loc = Expr::lnth(base.clone(), 0);
    let current_proj = Expr::lnth(base, 1);
    let total_proj = Expr::lst_concat(current_proj, proj.into());
    (loc, total_proj)
}

impl<'tcx> GilPlace<'tcx> {
    pub fn base_is_slice(&self) -> bool {
        matches!(self.base_ty.kind(), TyKind::Slice(..) | TyKind::Str)
    }

    pub fn into_loc_proj_meta(self) -> (Expr, Expr, Option<Expr>) {
        let base_is_slice = self.base_is_slice();
        let base = Expr::PVar(self.base);
        if base_is_slice {
            let addr = Expr::lnth(base.clone(), 0);
            let loc = Expr::lnth(addr.clone(), 0);
            let proj = Expr::lnth(addr, 1);
            let meta = Expr::lnth(base, 1);
            match &self.proj[..] {
                [] => (loc, proj, Some(meta)),
                [GilProj::Index(e), rest @ ..] => {
                    let actual_index = Expr::plus(e.clone(), meta);
                    let mut total_proj = Vec::with_capacity(self.proj.len());
                    total_proj.push(actual_index);
                    let mut rest_proj = rest.iter().map(|x| x.clone().into_expr()).collect();
                    total_proj.append(&mut rest_proj);
                    let (loc, total_proj) = add_proj_thin(loc, total_proj);
                    (loc, total_proj, None)
                }
                _ => panic!("Using something else than index on slice"),
            }
        } else {
            let proj: Vec<_> = self.proj.into_iter().map(|x| x.into_expr()).collect();
            let (loc, ofs) = add_proj_thin(base, proj);
            (loc, ofs, None)
        }
    }

    pub fn into_expr_ptr(self) -> Expr {
        if self.proj.is_empty() {
            return Expr::PVar(self.base);
        }
        let (loc, total_proj, meta) = self.into_loc_proj_meta();
        match meta {
            None => vec![loc, total_proj].into(),
            Some(meta) => vec![vec![loc, total_proj].into(), meta].into(),
        }
    }
}

pub enum MemoryAccess<'tcx> {
    InMemory(GilPlace<'tcx>),
    InStore(String),
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn push_read_gil_place_in_memory(
        &mut self,
        res: String,
        gil_place: GilPlace,
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

    fn push_write_gil_place_in_memory(&mut self, gil_place: GilPlace, value: Expr, typ: Ty<'tcx>) {
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
            base: self.name_from_local(&place.local),
            proj: vec![],
            base_ty: self.place_ty(&place.local.into()),
        };
        for (idx, proj) in place.projection.into_iter().enumerate() {
            match proj {
                ProjectionElem::Deref => {
                    let new_base = self.temp_var();
                    let typ = self.place_ty_until(place, idx);
                    self.push_read_gil_place_in_memory(new_base.clone(), cur_gil_place, typ, true);
                    cur_gil_place = GilPlace {
                        base: new_base,
                        proj: vec![],
                        base_ty: typ,
                    };
                }
                ProjectionElem::Field(u, _) => cur_gil_place.proj.push(GilProj::Field(u.as_u32())),
                ProjectionElem::Index(local) => {
                    // so depending if the local is in memory or in the store, this is going to change a lot!
                    // In the store? Fine! The index is just the variable corresponding to the local.
                    // In the memory? Gotta read first...
                    let expr = self.push_place_read(&local.into(), true);
                    cur_gil_place.proj.push(GilProj::Index(expr))
                }
                // Place pointer should contain their types? But so far, I think this has no effect.
                ProjectionElem::Downcast(_, u) => {
                    cur_gil_place.proj.push(GilProj::Downcast(u.as_u32()))
                }
                _ => fatal!(self, "Invalid projection element: {:#?}", proj),
            }
        }
        cur_gil_place
    }

    pub fn push_place_read(&mut self, place: &Place<'tcx>, copy: bool) -> Expr {
        let read_ty = self.place_ty(place);
        let gil_place = self.push_get_gil_place(place);
        self.push_read_gil_place(gil_place, read_ty, copy)
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
        let gil_place = self.push_get_gil_place(place);
        self.push_write_gil_place_in_memory(gil_place, value, value_ty);
    }
}
