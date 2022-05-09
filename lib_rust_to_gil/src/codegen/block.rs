use super::names::*;
use crate::prelude::*;

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_terminator(&mut self, terminator: &Terminator<'tcx>) {
        match &terminator.kind {
            TerminatorKind::FalseUnwind {
                real_target: target,
                ..
            }
            | TerminatorKind::FalseEdge {
                real_target: target,
                ..
            }
            | TerminatorKind::Goto { target } => {
                self.push_cmd(Cmd::Goto(bb_label(target)));
            }
            TerminatorKind::Return => {
                self.push_place_read_into(names::ret_var(), &Place::return_place(), false);
                self.push_cmd(Cmd::Goto(names::ret_label()));
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                // TODO: Handle cleanups at some point
                let mut gil_args = Vec::with_capacity(args.len());
                for arg in args {
                    gil_args.push(self.push_encode_operand(arg));
                }
                let fname = self.fname_from_operand(func).into();
                match destination {
                    Some((place, bb)) => {
                        let target = self.temp_var();
                        self.push_cmd(Cmd::Call {
                            variable: target.clone(),
                            parameters: gil_args,
                            proc_ident: fname,
                            error_lab: None,
                            bindings: None,
                        });
                        let call_ret_ty = self.place_ty(place);
                        self.push_place_write(place, Expr::PVar(target), call_ret_ty);
                        self.push_cmd(Cmd::Goto(bb_label(bb)));
                    }
                    None => {
                        let variable = names::unused_var();
                        self.push_cmd(Cmd::Call {
                            variable,
                            parameters: gil_args,
                            proc_ident: fname,
                            error_lab: None,
                            bindings: None,
                        })
                    }
                }
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
                let to_assert = if *expected { cond } else { !cond };
                let assert_call = runtime::lang_assert(to_assert, msg);
                self.push_cmd(assert_call);
                self.push_cmd(Cmd::Goto(bb_label(target)));
            }
            TerminatorKind::SwitchInt {
                discr,
                switch_ty: _,
                targets,
            } => {
                // FIXME: The switch ty should maybe be used at some point, when Gillian has ints...
                let discr_expr = self.push_encode_operand(discr);
                let mut else_lab = self.switch_label();
                for (value, target) in targets.iter() {
                    let v_expr = Expr::int(value as i64);
                    let target = bb_label(&target);
                    let goto = Cmd::GuardedGoto {
                        guard: Expr::eq_expr(discr_expr.clone(), v_expr),
                        then_branch: target,
                        else_branch: else_lab.clone(),
                    };
                    self.push_cmd(goto);
                    self.push_label(else_lab);
                    else_lab = self.switch_label();
                }
                let goto = Cmd::Goto(bb_label(&targets.otherwise()));
                self.push_cmd(goto)
            }
            TerminatorKind::Unreachable => {
                let cmd = Cmd::Fail {
                    name: "Unreachable".into(),
                    parameters: vec![],
                };
                self.push_cmd(cmd);
            }
            _ => fatal!(self, "Terminator not handled yet: {:#?}", terminator),
        }
    }

    pub fn push_basic_block(&mut self, bb: &BasicBlock, bb_data: &BasicBlockData<'tcx>) {
        if bb_data.is_cleanup {
            return;
        }
        self.push_label(bb_label(bb));
        log::debug!("----{:#?}----", bb);
        for stmt in &bb_data.statements {
            self.push_statement(stmt);
        }
        if let Some(terminator) = &bb_data.terminator {
            self.push_terminator(terminator);
        }
    }
}
