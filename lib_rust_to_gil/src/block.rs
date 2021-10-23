use super::body_ctx::BodyCtxt;
use super::names::*;
use gillian::gil::*;
use rustc_middle::mir::*;

impl<'gil, 'tcx> BodyCtxt<'gil, 'tcx> {
    pub fn compile_terminator(&self, terminator: &Terminator<'tcx>) -> Vec<ProcBodyItem> {
        match &terminator.kind {
            TerminatorKind::Goto { target } => {
                let cmd = Cmd::Goto(bb_label(&target));
                let item = ProcBodyItem::from(cmd);
                vec![item]
            }
            TerminatorKind::Return => {
                let cmd = Cmd::ReturnNormal;
                let item = ProcBodyItem::from(cmd);
                vec![item]
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                cleanup,
                ..
            } => {
                assert!(
                    args.is_empty(),
                    "Cannot handle function arguments yet! {:#?}",
                    terminator
                );
                assert!(
                    cleanup.is_none(),
                    "Don't know how to handle cleanups in calls yet"
                );
                assert!(destination.is_some(), "no destination for function call!");
                let (place, bb) = destination.unwrap();
                let fname = self.fname_from_operand(func);
                let call = Cmd::Call {
                    variable: self.compile_place(&place),
                    parameters: vec![],
                    proc_ident: Expr::string(fname),
                    error_lab: None,
                    bindings: None,
                };
                let item_call = ProcBodyItem::from(call);
                let goto = Cmd::Goto(bb_label(&bb));
                let item_goto = ProcBodyItem::from(goto);
                vec![item_call, item_goto]
            }
            _ => panic!("Terminator not handled yet: {:#?}", terminator),
        }
    }

    pub fn compile_basic_block(
        &self,
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
