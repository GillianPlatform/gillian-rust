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
                self.push_cmd(Cmd::Goto(bb_label(*target)));
            }
            TerminatorKind::Return => {
                self.push_place_read_into(names::ret_var(), Place::return_place(), false);
                self.push_cmd(Cmd::Goto(names::ret_label()));
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => self.push_function_call(func, args, *destination, *target),
            TerminatorKind::Assert {
                cond: op,
                expected,
                msg: _,
                target,
                unwind: _,
            } => {
                let msg = "Ugly assert message for now".to_string();
                let cond = self.push_encode_operand(op);
                let to_assert = if *expected { cond } else { !cond };
                let assert_call = runtime::lang_assert(to_assert, msg);
                self.push_cmd(assert_call);
                self.push_cmd(Cmd::Goto(bb_label(*target)));
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let switch_ty = self.operand_ty(discr);
                let discr_expr = self.push_encode_operand(discr);
                if switch_ty.is_bool() {
                    // We maintain the boolean abstraction, so we can't do a "normal" switch int.
                    // Instead, we're going to do a normal goto.
                    assert_eq!(targets.all_targets().len(), 2, "boolean is not 2");
                    let first_target_is_true =
                        targets.iter().next().expect("SwitchInt with no target").0 == 1;
                    let all_targets = targets.all_targets();
                    let (then_branch, else_branch) = if first_target_is_true {
                        (all_targets[0], all_targets[1])
                    } else {
                        (all_targets[1], all_targets[0])
                    };
                    let (then_branch, else_branch) =
                        (names::bb_label(then_branch), names::bb_label(else_branch));
                    let goto = Cmd::GuardedGoto {
                        guard: discr_expr,
                        then_branch,
                        else_branch,
                    };
                    self.push_cmd(goto);
                } else {
                    let mut else_lab = self.switch_label();
                    for (value, target) in targets.iter() {
                        let v_expr = Expr::int(value);
                        let target = bb_label(target);
                        let goto = Cmd::GuardedGoto {
                            guard: Expr::eq_expr(discr_expr.clone(), v_expr),
                            then_branch: target,
                            else_branch: else_lab.clone(),
                        };
                        self.push_cmd(goto);
                        self.push_label(else_lab);
                        else_lab = self.switch_label();
                    }
                    let goto = Cmd::Goto(bb_label(targets.otherwise()));
                    self.push_cmd(goto)
                }
            }
            TerminatorKind::Unreachable => {
                let cmd = Cmd::Fail {
                    name: "Unreachable".into(),
                    parameters: vec![],
                };
                self.push_cmd(cmd);
            }
            TerminatorKind::Drop { place, target, .. } => {
                log::warn!("Not handling drop properly yet: {:?}", place);
                let goto = Cmd::Goto(bb_label(*target));
                self.push_cmd(goto);
            }
            _ => fatal!(self, "Terminator not handled yet: {:#?}", terminator),
        }
    }

    pub fn push_basic_block(&mut self, bb: BasicBlock, bb_data: &BasicBlockData<'tcx>) {
        if bb_data.is_cleanup {
            return;
        }
        self.push_label(bb_label(bb));
        let mut loc = Location {
            block: bb,
            statement_index: 0,
        };
        for stmt in bb_data.statements.iter() {
            // let ix = self.location_table.start_index(loc);
            // let regions = self.polonius.origins_live_at(ix.as_usize().into());
            // let mix = self.location_table.mid_index(loc);
            // let mregions = self.polonius.origins_live_at(mix.as_usize().into());

            self.push_statement(stmt);
            loc = loc.successor_within_block();
        }
        // let ix = self.location_table.start_index(loc);
        // let regions = self.polonius.origins_live_at(ix.as_usize().into());

        // let mix = self.location_table.mid_index(loc);
        // let mregions = self.polonius.origins_live_at(mix.as_usize().into());


        self.push_terminator(bb_data.terminator())
    }
}
