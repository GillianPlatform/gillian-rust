use super::names::*;
use crate::prelude::*;

impl<'tcx> GilCtxt<'tcx> {
    pub fn push_terminator(&mut self, terminator: &Terminator<'tcx>) {
        match &terminator.kind {
            TerminatorKind::Goto { target } => {
                self.push_cmd(Cmd::Goto(bb_label(&target)));
            }
            TerminatorKind::Return => {
                self.push_cmd(Cmd::ReturnNormal);
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                cleanup,
                ..
            } => {
                assert!(
                    cleanup.is_none(),
                    "Don't know how to handle cleanups in calls yet"
                );
                assert!(destination.is_some(), "no destination for function call!");
                let mut gil_args = Vec::with_capacity(args.len());
                for arg in args {
                    gil_args.push(self.encode_operand(arg));
                }
                let (place, bb) = destination.unwrap();
                let fname = self.fname_from_operand(func);
                let encoded_place = self.encode_place(&place);
                let target = if encoded_place.is_var() {
                    self.place_base(&encoded_place)
                } else {
                    self.temp_var()
                };
                self.push_cmd(Cmd::Call {
                    variable: target.clone(),
                    parameters: gil_args,
                    proc_ident: Expr::string(fname),
                    error_lab: None,
                    bindings: None,
                });
                if !encoded_place.is_var() {
                    // If the place was not a var, we need to assign the result to the actual place.
                    self.push_assignment(&encoded_place, Expr::PVar(target));
                }
                self.push_cmd(Cmd::Goto(bb_label(&bb)));
            }
            TerminatorKind::Assert {
                cond: op,
                expected,
                msg: _,
                target,
                cleanup: _,
            } => {
                let msg = "Ugly assert message for now".to_string();
                let cond = self.encode_operand(op);
                let to_assert = if !expected { Expr::not(cond) } else { cond };
                let assert_call = runtime::lang_assert(to_assert, msg);
                self.push_cmd(assert_call);
                self.push_cmd(Cmd::Goto(bb_label(&target)));
            }
            _ => fatal!(self, "Terminator not handled yet: {:#?}", terminator),
        }
    }

    pub fn push_basic_block(&mut self, bb: &BasicBlock, bb_data: &BasicBlockData<'tcx>) {
        self.push_label(bb_label(bb));
        for stmt in &bb_data.statements {
            self.push_statement(&stmt);
        }
        if let Some(terminator) = &bb_data.terminator {
            self.push_terminator(&terminator);
        }
    }
}
