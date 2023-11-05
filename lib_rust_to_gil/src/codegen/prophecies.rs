use crate::prelude::*;

use rustc_middle::{mir::Place, ty::Ty};

use gillian::gil::Expr;

use super::context::GilCtxt;

mod action_names {
    pub(crate) const PCY_ALLOC: &str = "pcy_alloc";
}

pub enum ProphecyAction<'tcx> {
    Alloc(Ty<'tcx>),
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn push_pcy_action(&mut self, target: String, action: ProphecyAction<'tcx>) {
        match action {
            ProphecyAction::Alloc(ty) => {
                let ty = self.encode_type(ty).into();
                self.push_cmd(Cmd::Action {
                    variable: target,
                    action_name: action_names::PCY_ALLOC.to_string(),
                    parameters: vec![ty],
                })
            }
        }
    }

    fn push_alloc_prophecy(&mut self, typ: Ty<'tcx>) -> Expr {
        let action = ProphecyAction::Alloc(typ);
        let target = self.temp_var();
        self.push_pcy_action(target.clone(), action);
        Expr::PVar(target)
    }

    pub fn push_create_prophecy_for(&mut self, place: Place<'tcx>) -> Expr {
        if !self.prophecies_enabled() {
            fatal!(self, "Prophecies are not enabled, something is wrong");
        }
        let ty = self.place_ty(place).ty;
        match self.global_env().get_repr_ty_for(ty) {
            Some(repr_ty) => self.push_alloc_prophecy(repr_ty),
            None => Expr::null(),
        }
    }
}
