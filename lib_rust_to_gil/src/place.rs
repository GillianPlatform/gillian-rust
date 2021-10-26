use super::body_ctx::BodyCtxt;
use gillian::gil::*;
use rustc_middle::mir::*;

impl<'gil, 'tcx> BodyCtxt<'gil, 'tcx> {
    /* Returns the variable name. It should also probably return a Vec of commands to get there */
    pub fn encode_place(&self, place: &Place<'tcx>) -> (Vec<ProcBodyItem>, String) {
        if place.projection.len() == 0 {
            (vec![], self.name_from_local(&place.local))
        } else {
            panic!("Can't handle places with projection yet!");
        }
        
        
    }
}
