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

fn add_proj(base: String, proj: Vec<Expr>) -> (Expr, Expr) {
    let base = Expr::PVar(base);
    let loc = Expr::lnth(base.clone(), 0);
    let current_proj = Expr::lnth(base, 1);
    let proj = Expr::EList(proj);
    let total_proj = Expr::lst_concat(current_proj, proj);
    (loc, total_proj)
}

impl<'tcx> GilPlace<'tcx> {
    pub fn into_loc_proj(self) -> (Expr, Expr) {
        let proj = self.proj.into_iter().map(|x| x.into_expr()).collect();
        add_proj(self.base, proj)
    }

    pub fn into_expr_ptr(self) -> Expr {
        if self.proj.is_empty() {
            return Expr::PVar(self.base);
        }
        let proj = self.proj.into_iter().map(|x| x.into_expr()).collect();
        let (loc, total_proj) = add_proj(self.base, proj);
        Expr::EList(vec![loc, total_proj])
    }
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn push_read_gil_place_in_memory(
        &mut self,
        res: String,
        gil_place: GilPlace,
        typ: Ty<'tcx>,
        copy: bool,
    ) {
        let GilPlace { base, proj, .. } = gil_place;
        let proj = proj.into_iter().map(|x| x.into_expr()).collect();
        let (location, projection) = add_proj(base, proj);
        let action = MemoryAction::Load {
            location,
            projection,
            copy,
            typ,
        };
        self.push_action(res, action);
    }

    fn push_write_gil_place_in_memory(&mut self, gil_place: GilPlace, value: Expr, typ: Ty<'tcx>) {
        let GilPlace { base, proj, .. } = gil_place;
        let proj = proj.into_iter().map(|x| x.into_expr()).collect();

        let (location, projection) = add_proj(base, proj);
        let action = MemoryAction::Store {
            location,
            projection,
            typ,
            value,
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
