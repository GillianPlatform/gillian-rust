use crate::prelude::*;

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_statement(&mut self, stmt: &Statement<'tcx>) {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let compiled_rvalue = self.push_encode_rvalue(rvalue);
                self.push_place_write(*place, compiled_rvalue, self.rvalue_ty(rvalue));
            }
            StatementKind::Deinit(box place) => self.push_deinit_place(*place),
            StatementKind::SetDiscriminant { .. } => {
                let cmd = Cmd::Fail {
                    name: "SET_DISCR".to_owned(),
                    parameters: vec!["This statement only exists so we can compile constructors because they exist in MIR, but shouldn't be used".into()],
                };
                self.push_cmd(cmd);
            }
            StatementKind::PlaceMention(..)
            | StatementKind::FakeRead(..)
            | StatementKind::Nop
            | StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..)
            | StatementKind::AscribeUserType(..) => {}

            _ => fatal!(self, "Statement not handled yet: {:#?}", stmt),
        }
    }
}
