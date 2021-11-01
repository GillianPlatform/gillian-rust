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
                self.push_cmd(Cmd::Call {
                    variable: encoded_place,
                    parameters: vec![],
                    proc_ident: Expr::string(fname),
                    error_lab: None,
                    bindings: None,
                });
                self.push_cmd(Cmd::Goto(bb_label(&bb)));
            }
            _ => panic!("Terminator not handled yet: {:#?}", terminator),
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
