use rustc_middle::mir::Place;

use gillian::gil::Expr;

use super::context::GilCtxt;

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_create_prophecy_for(&mut self, _place: Place<'tcx>) -> Expr {
        // let ty = self.place_ty(place).ty;
        // let repr_ty_id = self
        //     .tcx
        //     .get_diagnostic_item(Symbol::intern("gillian::repr::shallow_model_ty"))
        //     .expect("Couldn't find gilogic::repr::shallow_model_ty");
        // let trait_id = self
        //     .tcx
        //     .trait_of_item(repr_ty_id)
        //     .expect("Ty is not in a trait??");
        // let trait_ref = Binder::dummy(TraitRef::new(
        //     trait_id,
        //     self.tcx.intern_substs(&[ty.into()]),
        // ));
        // dbg!(ty, trait_ref);
        // panic!("bite");
        [Expr::null(), vec![].into()].into()
    }
}
