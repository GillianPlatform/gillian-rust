use crate::prelude::*;

impl<'tcx> GilCtxt<'tcx> {
    pub fn push_statement(&mut self, stmt: &Statement<'tcx>) {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let encoded_place = self.encode_place(place);
                let compiled_rvalue = self.compile_rvalue(rvalue);
                self.push_assignment(&encoded_place, compiled_rvalue);
            }
            _ => fatal!(self, "Statment not handled yet: {:#?}", stmt),
        }
    }
}
