use crate::prelude::*;

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_statement(&mut self, stmt: &Statement<'tcx>) {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let compiled_rvalue = self.push_encode_rvalue(rvalue);
                self.push_place_write(place, compiled_rvalue, self.rvalue_ty(rvalue));
            }
            _ => fatal!(self, "Statment not handled yet: {:#?}", stmt),
        }
    }
}
