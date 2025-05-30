use crate::prelude::*;

use gillian::gil::Expr;

use super::context::GilCtxt;

mod action_names {
    pub(crate) const PCY_ALLOC: &str = "pcy_alloc";
}

pub enum ProphecyAction {
    Alloc,
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn push_pcy_action(&mut self, target: String, action: ProphecyAction) {
        match action {
            ProphecyAction::Alloc => self.push_cmd(Cmd::Action {
                variable: target,
                action_name: action_names::PCY_ALLOC.to_string(),
                parameters: vec![],
            }),
        }
    }

    pub fn push_alloc_prophecy(&mut self) -> Expr {
        if !self.prophecies_enabled() {
            fatal!(self, "Prophecies are not enabled, something is wrong");
        }
        let action = ProphecyAction::Alloc;
        let target = self.temp_var();
        self.push_pcy_action(target.clone(), action);
        Expr::PVar(target).lnth(0)
    }

    //
    // pub fn push_create_prophecy_for(&mut self, place: Place<'tcx>) -> Expr {
    //     let ty = self.place_ty(place).ty;
    //     match self.global_env().get_repr_ty_for(ty) {
    //         Some(repr_ty) => self.push_alloc_prophecy(),
    //         None => Expr::null(),
    //     }
    // }
}
