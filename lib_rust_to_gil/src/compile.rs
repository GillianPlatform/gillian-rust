use std::vec::Vec;

use crate::names::bb_label;

use super::body_ctx::BodyCtxt;
use super::gil::*;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::Constant as MirConstant;
use rustc_middle::mir::*;
use rustc_middle::ty::{Const, ConstKind, TyCtxt, TyKind};
use rustc_target::abi::Size;
use std::convert::TryInto;

// Here, we're talking a lot of inspiration from the semantics described by the MIR interpreter :
// https://doc.rust-lang.org/stable/nightly-rustc/src/rustc_mir/interpret/step.rs.html

pub struct ToGilTyCtxt<'gil, 'tcx>(&'gil TyCtxt<'tcx>);

impl<'gil, 'tcx> ToGilTyCtxt<'gil, 'tcx> {
    pub fn new(tcx: &'gil TyCtxt<'tcx>) -> Self {
        ToGilTyCtxt(tcx)
    }

    /* Returns the variable name. It should also probably return a Vec of commands to get there */
    pub fn compile_place(&self, place: &Place<'tcx>, body_ctx: &BodyCtxt<'gil, 'tcx>) -> String {
        if place.projection.len() != 0 {
            panic!("Can't handle places with projection yet!");
        }
        body_ctx.name_from_local(&place.local)
    }

    pub fn compile_rvalue(&self, rvalue: &Rvalue<'tcx>, _body_ctx: &BodyCtxt<'gil, 'tcx>) -> Expr {
        match rvalue {
            Rvalue::Use(Operand::Constant(box MirConstant {
                literal:
                    ConstantKind::Ty(Const {
                        val: ConstKind::Value(ConstValue::Scalar(Scalar::Int(scalar_int))),
                        ..
                    }),
                ..
            })) => {
                let x: i64 = scalar_int
                    .to_bits(scalar_int.size())
                    .unwrap()
                    .try_into()
                    .unwrap();
                Expr::Lit(Literal::Int(x))
            }
            _ => panic!("Unhandled rvalue: {:#?}", rvalue),
        }
    }

    /* Returns the variable name */
    pub fn compile_assignment(
        &self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        body_ctx: &BodyCtxt<'gil, 'tcx>,
    ) -> Cmd {
        let variable = self.compile_place(place, body_ctx);
        let assigned_expr = self.compile_rvalue(rvalue, body_ctx);
        Cmd::Assignment {
            variable,
            assigned_expr,
        }
    }

    pub fn compile_statement(
        &self,
        stmt: &Statement<'tcx>,
        body_ctx: &BodyCtxt<'gil, 'tcx>,
    ) -> Vec<ProcBodyItem> {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let cmd = self.compile_assignment(place, rvalue, body_ctx);
                let item = ProcBodyItem::from(cmd);
                vec![item]
            }
            _ => panic!("Statment not handled yet: {:#?}", stmt),
        }
    }

    pub fn is_zst(val: &ConstKind) -> bool {
        match val {
            ConstKind::Value(ConstValue::Scalar(Scalar::Int(sci))) => sci.size() == Size::ZERO,
            _ => false,
        }
    }

    pub fn fname_from_operand(&self, operand: &Operand<'tcx>, _body_ctx: &BodyCtxt<'gil, 'tcx>) -> String {
        match &operand {
            Operand::Constant(box MirConstant {
                literal: ConstantKind::Ty(Const { ty, val }),
                ..
            }) if Self::is_zst(val) && ty.is_fn() => {
                match ty.kind() {
                    TyKind::FnDef(did, _) => self.0.item_name(*did).to_string(),
                    tyk => panic!("unhandled TyKind for function name: {:#?}", tyk)
                }
            }
            _ => panic!(
                "Can't handle dynami calls yet! Got fun operand: {:#?}",
                operand
            ),
        }
    }

    pub fn compile_terminator(
        &self,
        terminator: &Terminator<'tcx>,
        body_ctx: &BodyCtxt<'gil, 'tcx>,
    ) -> Vec<ProcBodyItem> {
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
                assert!(args.is_empty(), "Cannot handle function arguments yet! {:#?}", terminator);
                assert!(
                    cleanup.is_none(),
                    "Don't know how to handle cleanups in calls yet"
                );
                assert!(destination.is_some(), "no destination for function call!");
                let (place, bb) = destination.unwrap();
                let fname = self.fname_from_operand(func, body_ctx);
                let call = Cmd::Call {
                    variable: self.compile_place(&place, body_ctx),
                    parameters: vec![],
                    proc_ident: Expr::string(fname),
                    error_lab: None,
                    bindings: None
                };
                let item_call = ProcBodyItem::from(call);
                let goto = Cmd::Goto(bb_label(&bb));
                let item_goto = ProcBodyItem::from(goto);
                vec![item_call, item_goto]
            }
            _ => panic!("Terminator not handled yet: {:#?}", terminator),
        }
    }

    fn set_first_label(body_items: &mut Vec<ProcBodyItem>, label: String) {
        assert!(!body_items.is_empty());
        let item = body_items.get_mut(0).unwrap();
        item.label = Some(label);
    }

    pub fn compile_basic_block(
        &self,
        bb: &BasicBlock,
        bb_data: &BasicBlockData<'tcx>,
        body_ctx: &BodyCtxt<'gil, 'tcx>,
    ) -> Vec<ProcBodyItem> {
        let mut compiled_block: Vec<ProcBodyItem> = bb_data
            .statements
            .iter()
            .flat_map(|stmt| self.compile_statement(&stmt, body_ctx))
            .collect();
        if let Some(terminator) = &bb_data.terminator {
            compiled_block.append(&mut self.compile_terminator(&terminator, body_ctx));
        }
        ToGilTyCtxt::set_first_label(&mut compiled_block, bb_label(bb));
        compiled_block
    }

    pub fn compile_body(&'gil self, key: &LocalDefId) -> Proc {
        let did = key.to_def_id();
        let proc_name = self.0.item_name(did);
        let mir_body = self.0.optimized_mir(did);
        let body_ctx = BodyCtxt::new(mir_body, &self.0);
        log::debug!("{} : {:#?}", proc_name, mir_body);
        if mir_body.is_polymorphic {
            panic!("Polymorphism is not handled yet.")
        }
        if mir_body.generator_kind().is_some() {
            panic!("Generators are not handled yet.")
        }

        // let ret_ptr = mir_body.local_decls.get(RETURN_PLACE);
        let args: Vec<String> = mir_body
            .args_iter()
            .map(|local| body_ctx.original_name_from_local(&local).unwrap())
            .collect();
        let compiled_body: Vec<ProcBodyItem> = mir_body
            .basic_blocks()
            .iter_enumerated()
            .flat_map(|(bb, bb_data)| self.compile_basic_block(&bb, &bb_data, &body_ctx))
            .collect();
        Proc::new(proc_name.to_string(), args, compiled_body)
    }

    pub fn compile_prog(&'gil self) -> Prog {
        let procs: Vec<Proc> = self
            .0
            .mir_keys(())
            .iter()
            .map(|key| self.compile_body(key))
            .collect();
        for proc in procs {
            println!("{}", proc);
        }
        // let mir_main = self.0.optimized_mir(*key);
        // log::debug!("{:#?}", mir_main);
        // let gil_main = self.compile_function(mir_main);
        // log::debug!("{:#?}", gil_main);
        Prog::default()
    }
}
