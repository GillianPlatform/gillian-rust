use super::body_ctx::BodyCtxt;
use rustc_middle::mir::*;

impl<'gil, 'tcx> BodyCtxt<'gil, 'tcx> {
    /* Returns the variable name. It should also probably return a Vec of commands to get there */
    pub fn compile_place(&self, place: &Place<'tcx>) -> String {
        if place.projection.len() != 0 {
            panic!("Can't handle places with projection yet!");
        }
        self.name_from_local(&place.local)
    }
}
