use crate::codegen::runtime;
use crate::prelude::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
// use rustc_middle::ty::Ty;
use rustc_middle::ty::{Const, ConstKind};

impl<'tcx> GilCtxt<'tcx> {
    pub fn compile_rvalue(&mut self, rvalue: &Rvalue<'tcx>) -> Expr {
        match rvalue {
            Rvalue::Use(operand) => self.encode_operand(operand),
            Rvalue::CheckedBinaryOp(binop, box (left, right)) => {
                self.encode_binop(binop, left, right)
            }
            _ => fatal!(self, "Unhandled rvalue: {:#?}", rvalue),
        }
    }

    pub fn encode_binop(
        &mut self,
        binop: &mir::BinOp,
        left: &Operand<'tcx>,
        right: &Operand<'tcx>,
    ) -> Expr {
        let e1 = self.encode_operand(left);
        let e2 = self.encode_operand(right);
        let left_ty = self.operand_ty(left);
        let right_ty = self.operand_ty(right);
        assert!(TyS::same_type(left_ty, right_ty));
        match binop {
            mir::BinOp::Add if left_ty.is_numeric() => {
                let max_val = left_ty.numeric_max_val(self.ty_ctxt).unwrap();
                let max_val = self.encode_const(max_val);
                let temp = self.temp_var();
                self.push_cmd(runtime::checked_add(temp.clone(), e1, e2, max_val));
                Expr::PVar(temp)
            }
            mir::BinOp::Add => fatal!(
                self,
                "Adding non-numeric values: {:#?} and {:#?}",
                left,
                right
            ),
            _ => fatal!(
                self,
                "Cannot yet encode binop {:#?} with operands {:#?} and {:#?}",
                binop,
                left,
                right
            ),
        }
        // Expr::BinOp {
        //     operator: gil::BinOp::IPlus,
        //     left_operand,
        //     right_operand,
        // }
        // match binop {
        //     Add when
        // }
    }

    /// Returns a series of GIL commands necessary to access a place, as well as the
    /// name of the variable that will contain the place in the end.
    pub fn encode_operand(&mut self, operand: &Operand<'tcx>) -> Expr {
        match operand {
            Operand::Constant(box cst) => self.encode_constant(cst),
            Operand::Move(place) => {
                let temp = self.temp_var();
                let s = self.encode_place(place);
                self.push_cmd(Cmd::Assignment {
                    variable: temp.clone(),
                    assigned_expr: self.place_read(&s),
                });
                self.push_assignment(&s, Expr::Lit(Literal::Nono));
                Expr::PVar(temp)
            }
            Operand::Copy(place) => self.place_read(&self.encode_place(place)),
        }
    }

    pub fn encode_constant(&self, constant: &mir::Constant) -> Expr {
        match constant.literal {
            ConstantKind::Ty(cst) => self.encode_const(cst),
            _ => fatal!(self, "Cannot encode constant yet! {:#?}", constant),
        }
    }

    pub fn encode_const(&self, cst: &Const) -> Expr {
        match cst {
            Const {
                val: ConstKind::Value(ConstValue::Scalar(Scalar::Int(scalar_int))),
                ..
            } => {
                let x: i64 = scalar_int
                    .to_bits(scalar_int.size())
                    .unwrap()
                    .try_into()
                    .unwrap();
                Expr::Lit(Literal::Int(x))
            }
            _ => fatal!(self, "Cannot encode const yet! {:#?}", cst),
        }
    }

    pub fn fname_from_operand(&self, operand: &Operand<'tcx>) -> String {
        match &operand {
            Operand::Constant(box mir::Constant {
                literal: ConstantKind::Ty(Const { ty, val }),
                ..
            }) if Self::is_zst(val) && ty.is_fn() => match ty.kind() {
                TyKind::FnDef(did, _) => self.ty_ctxt.item_name(*did).to_string(),
                tyk => fatal!(self, "unhandled TyKind for function name: {:#?}", tyk),
            },
            _ => fatal!(
                self,
                "Can't handle dynami calls yet! Got fun operand: {:#?}",
                operand
            ),
        }
    }
}
