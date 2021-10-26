use super::body_ctx::BodyCtxt;
use super::names::*;
use gillian::gil::*;
use rustc_middle::mir::*;

impl<'gil, 'tcx> BodyCtxt<'gil, 'tcx> {
    pub fn compile_terminator(&mut self, terminator: &Terminator<'tcx>) -> Vec<ProcBodyItem> {
        match &terminator.kind {
            TerminatorKind::Goto { target } => {
                let cmd = Cmd::Goto(bb_label(&target));
                vec![cmd.into()]
            }
            TerminatorKind::Return => {
                let cmd = Cmd::ReturnNormal;
                vec![cmd.into()]
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
                let mut compiled_terminator = vec![]; 
                let mut gil_args = Vec::with_capacity(args.len());
                for arg in args {
                    let (mut ops, v) = self.encode_operand(arg);
                    compiled_terminator.append(&mut ops);
                    gil_args.push(v);
                }
                let (place, bb) = destination.unwrap();
                let fname = self.fname_from_operand(func);
                let (mut place_ops, encoded_place) = self.encode_place(&place);
                compiled_terminator.append(&mut place_ops);
                let call = Cmd::Call {
                    variable: encoded_place,
                    parameters: vec![],
                    proc_ident: Expr::string(fname),
                    error_lab: None,
                    bindings: None,
                };
                compiled_terminator.push(call.into());
                let goto = Cmd::Goto(bb_label(&bb));
                compiled_terminator.push(goto.into());
                compiled_terminator
            }
            _ => panic!("Terminator not handled yet: {:#?}", terminator),
        }
    }

    pub fn compile_basic_block(
        &mut self,
        bb: &BasicBlock,
        bb_data: &BasicBlockData<'tcx>,
    ) -> Vec<ProcBodyItem> {
        let mut compiled_block: Vec<ProcBodyItem> = bb_data
            .statements
            .iter()
            .flat_map(|stmt| self.compile_statement(&stmt))
            .collect();
        if let Some(terminator) = &bb_data.terminator {
            compiled_block.append(&mut self.compile_terminator(&terminator));
        }
        proc_body::set_first_label(&mut compiled_block, bb_label(bb));
        compiled_block
    }
}
