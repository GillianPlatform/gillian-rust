use crate::prelude::*;

impl<'tcx> GilCtxt<'tcx> {
    /* Returns the variable name. It should also probably return a Vec of commands to get there */
    pub fn encode_place(&self, place: &Place<'tcx>) -> String {
        if place.projection.len() == 0 {
            self.name_from_local(&place.local)
        } else {
            fatal!(self, "Can't handle places with projection yet!");
        }
    }
}
