use crate::prelude::*;

use rustc_middle::{
    mir::Place,
    ty::{Binder, ProjectionTy, TraitRef, Ty},
};
use rustc_span::Symbol;

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
        let ty = self.place_ty(place).ty;
        let repr_ty_id = self
            .tcx()
            .get_diagnostic_item(Symbol::intern("gillian::ownable::representation_ty"))
            .expect("Couldn't find gillian::ownable::representation_ty");
        // let trait_id = self
        //     .tcx
        //     .trait_of_item(repr_ty_id)
        //     .expect("Ty is not in a trait??");
        let t_subst = self.tcx().intern_substs(&[ty.into()]);
        // let trait_ref = Binder::dummy(TraitRef::new(trait_id, t_subst));
        let associated_type = self.tcx().mk_ty(TyKind::Projection(ProjectionTy {
            substs: t_subst,
            item_def_id: repr_ty_id,
        }));
        self.push_alloc_prophecy(associated_type)
    }
}
