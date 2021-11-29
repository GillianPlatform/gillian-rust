use super::names::*;
use crate::prelude::*;

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_terminator(&mut self, terminator: &Terminator<'tcx>) {
        match &terminator.kind {
            TerminatorKind::Goto { target } => {
                self.push_cmd(Cmd::Goto(bb_label(target)));
            }
            TerminatorKind::Return => {
                self.push_place_read_into(names::ret_var(), &Place::return_place(), false);
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
                    gil_args.push(self.push_encode_operand(arg));
                }
                let (place, bb) = destination.unwrap();
                let write_directly_in_var =
                    place.projection.is_empty() && !self.place_is_in_memory(&place);
                let target = if write_directly_in_var {
                    self.name_from_local(&place.local)
                } else {
                    self.temp_var()
                };
                let fname = self.fname_from_operand(func);
                self.push_cmd(Cmd::Call {
                    variable: target.clone(),
                    parameters: gil_args,
                    proc_ident: Expr::string(fname),
                    error_lab: None,
                    bindings: None,
                });
                if !write_directly_in_var {
                    let call_ret_ty = self.place_ty(&place);
                    self.push_place_write(&place, Expr::PVar(target), call_ret_ty);
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
                let cond = self.push_encode_operand(op);
                let to_assert = if !expected { !cond } else { cond };
                let assert_call = runtime::lang_assert(to_assert, msg);
                self.push_cmd(assert_call);
                self.push_cmd(Cmd::Goto(bb_label(target)));
            }
            _ => fatal!(self, "Terminator not handled yet: {:#?}", terminator),
        }
    }

    pub fn push_basic_block(&mut self, bb: &BasicBlock, bb_data: &BasicBlockData<'tcx>) {
        self.push_label(bb_label(bb));
        log::debug!("----{:#?}----", bb);
        for stmt in &bb_data.statements {
            // log::debug!("Pushing statement: {:#?}", stmt); // Somehow, this may panic..
            self.push_statement(stmt);
        }
        if let Some(terminator) = &bb_data.terminator {
            self.push_terminator(terminator);
        }
    }
}
