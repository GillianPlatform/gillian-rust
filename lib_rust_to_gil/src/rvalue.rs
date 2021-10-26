use crate::body_ctx::BodyCtxt;
use gillian::gil::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::Constant as MirConstant;
use rustc_middle::mir::*;
// use rustc_middle::ty::Ty;
use rustc_middle::ty::{Const, ConstKind, TyKind};
use std::convert::TryInto;

impl<'gil, 'tcx> BodyCtxt<'gil, 'tcx> {
    pub fn compile_rvalue(&mut self, rvalue: &Rvalue<'tcx>) -> (Vec<ProcBodyItem>, Expr) {
        match rvalue {
            Rvalue::Use(operand) => self.encode_operand(operand),
            Rvalue::CheckedBinaryOp(_binop, box (left, right)) => {
                let (mut v1, _e1) = self.encode_operand(left);
                let (mut v2, _e2) = self.encode_operand(right);
                v1.append(&mut v2);
                panic!("Cannot handle checked binops yet! {:#?}", rvalue)
                // let (mut v3, res) = self.encode_binop(binop, v1, v2, self.ty_ctxt.);
                // v1.append(v3);
                // (v1, res)
            }
            _ => panic!("Unhandled rvalue: {:#?}", rvalue),
        }
    }
    
    // pub fn encode_binop(&mut self, left: &Operand<'tcx>, right: &Operand<'tcx>, left_ty: &Ty, right_ty: &Ty) {
        
    // }

    /// Returns a series of GIL commands necessary to access a place, as well as the
    /// name of the variable that will contain the place in the end.
    pub fn encode_operand(&mut self, operand: &Operand<'tcx>) -> (Vec<ProcBodyItem>, Expr) {
        match operand {
            Operand::Constant(box cst) => (vec![], self.encode_constant(cst)),
            Operand::Move(place) => {
                let temp = self.temp_var();
                let (mut body, s) = self.encode_place(place);
                let assign_temp = Cmd::Assignment {
                    variable: temp.clone(),
                    assigned_expr: Expr::PVar(s.clone()),
                };
                let clear_place = Cmd::Assignment {
                    variable: s,
                    assigned_expr: Expr::Lit(Literal::Nono),
                };
                body.push(assign_temp.into());
                body.push(clear_place.into());
                (body, Expr::PVar(temp))
            }
            Operand::Copy(place) => {
                let (vec, s) = self.encode_place(place);
                (vec, Expr::PVar(s))
            }
        }
    }

    pub fn encode_constant(&self, constant: &MirConstant) -> Expr {
        match constant.literal {
            ConstantKind::Ty(Const {
                val: ConstKind::Value(ConstValue::Scalar(Scalar::Int(scalar_int))),
                ..
            }) => {
                let x: i64 = scalar_int
                    .to_bits(scalar_int.size())
                    .unwrap()
                    .try_into()
                    .unwrap();
                Expr::Lit(Literal::Int(x))
            }
            _ => panic!("Cannot encode constant yet! {:#?}", constant)
        }
    }

    pub fn fname_from_operand(&self, operand: &Operand<'tcx>) -> String {
        match &operand {
            Operand::Constant(box MirConstant {
                literal: ConstantKind::Ty(Const { ty, val }),
                ..
            }) if Self::is_zst(val) && ty.is_fn() => match ty.kind() {
                TyKind::FnDef(did, _) => self.ty_ctxt.item_name(*did).to_string(),
                tyk => panic!("unhandled TyKind for function name: {:#?}", tyk),
            },
            _ => panic!(
                "Can't handle dynami calls yet! Got fun operand: {:#?}",
                operand
            ),
        }
    }
}
