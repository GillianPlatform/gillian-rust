use super::memory::MemoryAction;
use crate::prelude::*;

pub struct GilPlace<'tcx> {
    pub base: String,
    pub base_ty: Ty<'tcx>,
    pub proj: Vec<usize>,
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
    pub fn into_expr_ptr(self) -> Expr {
        if self.proj.is_empty() {
            return Expr::PVar(self.base);
        }
        let proj = self.proj.iter().map(|x| Expr::int(*x as i64)).collect();
        let (loc, total_proj) = add_proj(self.base, proj);
        Expr::EList(vec![loc, total_proj])
    }
}

pub enum PlaceAccess<'tcx> {
    InMemory(GilPlace<'tcx>),
    InStore(GilPlace<'tcx>),
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn place_is_in_memory(&self, place: &Place) -> bool {
        self.is_referenced(&place.local)
    }

    fn push_read_gil_place_in_memory(
        &mut self,
        res: String,
        gil_place: GilPlace,
        typ: Ty<'tcx>,
        copy: bool,
    ) {
        let GilPlace { base, proj, .. } = gil_place;
        let proj = proj.iter().map(|x| Expr::int(*x as i64)).collect();
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
        let proj = proj.iter().map(|x| Expr::int(*x as i64)).collect();
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

    fn push_read_place_access(
        &mut self,
        access: PlaceAccess<'tcx>,
        read_ty: Ty<'tcx>,
        copy: bool,
    ) -> Expr {
        match access {
            PlaceAccess::InMemory(gil_place) => {
                let ret = self.temp_var();
                self.push_read_gil_place_in_memory(ret.clone(), gil_place, read_ty, copy);
                Expr::PVar(ret)
            }
            PlaceAccess::InStore(gil_place) => {
                let read_expr = self.reader_expr_for_place_in_store(&gil_place);
                if copy {
                    read_expr
                } else {
                    let ret_var = self.temp_var();
                    let ret = Expr::PVar(ret_var.clone());
                    let assign = Cmd::Assignment {
                        variable: ret_var,
                        assigned_expr: read_expr,
                    };
                    self.push_cmd(assign);
                    let write_expr = self.writer_expr_for_place_in_store(
                        Expr::Lit(Literal::Empty),
                        &gil_place,
                        &self.type_in_store_encoding(gil_place.base_ty),
                    );
                    let assign = Cmd::Assignment {
                        variable: gil_place.base,
                        assigned_expr: write_expr,
                    };
                    self.push_cmd(assign);
                    ret
                }
            }
        }
    }

    pub fn push_get_place_access(&mut self, place: &Place<'tcx>) -> PlaceAccess<'tcx> {
        let mut in_store = !self.place_is_in_memory(place);
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
                    if in_store {
                        let place = self.reader_expr_for_place_in_store(&cur_gil_place);
                        self.push_cmd(Cmd::Assignment {
                            variable: new_base.clone(),
                            assigned_expr: place,
                        });
                        in_store = false;
                    } else {
                        self.push_read_gil_place_in_memory(
                            new_base.clone(),
                            cur_gil_place,
                            typ,
                            true,
                        );
                    }
                    cur_gil_place = GilPlace {
                        base: new_base,
                        proj: vec![],
                        base_ty: typ,
                    };
                }
                ProjectionElem::Field(u, _) => cur_gil_place.proj.push(u.as_u32() as usize),
                _ => fatal!(self, "Invalid projection element: {:#?}", proj),
            }
        }
        if in_store {
            PlaceAccess::InStore(cur_gil_place)
        } else {
            PlaceAccess::InMemory(cur_gil_place)
        }
    }

    pub fn push_place_read(&mut self, place: &Place<'tcx>, copy: bool) -> Expr {
        let read_ty = self.place_ty(place);
        let access = self.push_get_place_access(place);
        self.push_read_place_access(access, read_ty, copy)
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
        match self.push_get_place_access(place) {
            PlaceAccess::InMemory(place) => {
                self.push_write_gil_place_in_memory(place, value, value_ty)
            }
            PlaceAccess::InStore(gil_place) => {
                let enc = self.type_in_store_encoding(self.place_ty(&place.local.into()));
                let write_expr = self.writer_expr_for_place_in_store(value, &gil_place, &enc);
                let assign = Cmd::Assignment {
                    variable: gil_place.base,
                    assigned_expr: write_expr,
                };
                self.push_cmd(assign)
            }
        }
    }
}
