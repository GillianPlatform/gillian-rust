use super::memory::MemoryAction;
use crate::prelude::*;

fn add_proj(base: String, proj: Vec<Expr>) -> (Expr, Expr) {
    let base = Expr::PVar(base);
    let loc = Expr::lnth(base.clone(), 0);
    let current_proj = Expr::lnth(base, 1);
    let proj = Expr::EList(proj);
    let total_proj = Expr::lst_concat(current_proj, proj);
    (loc, total_proj)
}

impl<'tcx> GilCtxt<'tcx> {
    fn push_no_deref_place_read(
        &mut self,
        res: String,
        base: String,
        proj: Vec<Expr>,
        typ: Ty<'tcx>,
        copy: bool,
    ) {
        let (location, projection) = add_proj(base, proj);
        let action = MemoryAction::Load {
            location,
            projection,
            copy,
            typ,
        };
        self.push_action(res, action);
    }

    fn push_no_deref_place_write(
        &mut self,
        base: String,
        proj: Vec<Expr>,
        value: Expr,
        typ: Ty<'tcx>,
    ) {
        let (location, projection) = add_proj(base, proj);
        let action = MemoryAction::Store {
            location,
            projection,
            typ,
            value,
        };
        let ret = self.temp_var();
        self.push_action(ret, action);
    }

    fn encode_projection_elem(&self, _proj: &ProjectionElem<Local, Ty<'tcx>>) -> Expr {
        Expr::Lit(Literal::Undefined)
    }

    pub fn push_get_place_pointer_no_deref(&mut self, place: &Place<'tcx>) -> (String, Vec<Expr>) {
        let mut cur_base = self.name_from_local(&place.local);
        let mut cur_proj = vec![];
        for (idx, proj) in place.projection.into_iter().enumerate() {
            match proj {
                ProjectionElem::Deref => {
                    let typ = self.place_ty_until(place, idx);
                    let new_base = self.temp_var();
                    self.push_no_deref_place_read(new_base.clone(), cur_base, cur_proj, typ, true);
                    cur_proj = vec![];
                    cur_base = new_base;
                }
                _ => {
                    let encoded_proj_elem = self.encode_projection_elem(&proj);
                    cur_proj.push(encoded_proj_elem)
                }
            }
        }
        (cur_base, cur_proj)
    }

    pub fn push_place_read_into(&mut self, ret: String, place: &Place<'tcx>, copy: bool) {
        let (base, proj) = self.push_get_place_pointer_no_deref(place);
        self.push_no_deref_place_read(ret, base, proj, self.place_ty(place), copy);
    }

    pub fn push_place_read(&mut self, place: &Place<'tcx>, copy: bool) -> String {
        let res = self.temp_var();
        self.push_place_read_into(res.clone(), place, copy);
        res
    }

    pub fn push_place_write(&mut self, place: &Place<'tcx>, value: Expr, value_ty: Ty<'tcx>) {
        let (base, proj) = self.push_get_place_pointer_no_deref(place);
        self.push_no_deref_place_write(base, proj, value, value_ty);
    }
}
