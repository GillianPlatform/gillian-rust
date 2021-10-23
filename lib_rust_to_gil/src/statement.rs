use gillian::gil::*;
use rustc_middle::mir::*;

use crate::body_ctx::BodyCtxt;

impl<'gil, 'tcx> BodyCtxt<'gil, 'tcx> {
    /* Returns the variable name */
    pub fn compile_assignment(&self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>) -> Cmd {
        let variable = self.compile_place(place);
        let assigned_expr = self.compile_rvalue(rvalue);
        Cmd::Assignment {
            variable,
            assigned_expr,
        }
    }

    pub fn compile_statement(&self, stmt: &Statement<'tcx>) -> Vec<ProcBodyItem> {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let cmd = self.compile_assignment(place, rvalue);
                let item = ProcBodyItem::from(cmd);
                vec![item]
            }
            _ => panic!("Statment not handled yet: {:#?}", stmt),
        }
    }
}
