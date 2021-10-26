use gillian::gil::*;
use rustc_middle::mir::*;

use crate::body_ctx::BodyCtxt;

impl<'gil, 'tcx> BodyCtxt<'gil, 'tcx> {
    /* Returns the variable name */
    pub fn compile_assignment(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>) -> Vec<ProcBodyItem> {
        
        let (mut pre, variable) = self.encode_place(place);
        let (mut expr_ops, assigned_expr) = self.compile_rvalue(rvalue);
        pre.append(&mut expr_ops);
        let cmd = Cmd::Assignment {
            variable,
            assigned_expr,
        };
        pre.push(cmd.into());
        pre
    }

    pub fn compile_statement(&mut self, stmt: &Statement<'tcx>) -> Vec<ProcBodyItem> {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                self.compile_assignment(place, rvalue)
            }
            _ => panic!("Statment not handled yet: {:#?}", stmt),
        }
    }
}
