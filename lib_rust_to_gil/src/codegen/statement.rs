use crate::prelude::*;

impl<'tcx> GilCtxt<'tcx> {
    /* Returns the variable name */
    pub fn push_assignment(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>) {
        let variable = self.encode_place(place);
        let assigned_expr = self.compile_rvalue(rvalue);
        self.push_cmd(Cmd::Assignment {
            variable,
            assigned_expr,
        });
    }

    pub fn push_statement(&mut self, stmt: &Statement<'tcx>) {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => self.push_assignment(place, rvalue),
            _ => panic!("Statment not handled yet: {:#?}", stmt),
        }
    }
}
