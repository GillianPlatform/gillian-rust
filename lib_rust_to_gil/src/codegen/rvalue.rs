use crate::codegen::runtime;
use crate::prelude::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::ty::{self, Const, ConstKind, TypeFoldable};

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_encode_rvalue(&mut self, rvalue: &Rvalue<'tcx>) -> Expr {
        match rvalue {
            Rvalue::Use(operand) => self.push_encode_operand(operand),
            Rvalue::CheckedBinaryOp(binop, box (left, right)) => {
                self.encode_binop(binop, left, right)
            }
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                // I need to know how to handle the BorrowKind
                // I don't know what needs to be done, maybe nothing
                let access = self.push_get_place_access(place);
                let gil_place = match access {
                    PlaceAccess::InStore(..) => {
                        fatal!(self, "Reference to something in the store!")
                    }
                    PlaceAccess::InMemory(gp) => gp,
                };
                gil_place.into_expr_ptr()
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
        let e1 = self.push_encode_operand(left);
        let e2 = self.push_encode_operand(right);
        let left_ty = self.operand_ty(left);
        let right_ty = self.operand_ty(right);
        assert!(TyS::same_type(left_ty, right_ty));
        match binop {
            mir::BinOp::Add if left_ty.is_numeric() => {
                let max_val = left_ty.numeric_max_val(self.ty_ctxt).unwrap();
                let max_val = self.encode_const(max_val);
                let temp = self.temp_var();
                self.push_cmd(runtime::checked_add(
                    temp.clone(),
                    e1,
                    e2,
                    Expr::Lit(max_val),
                ));
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
    pub fn push_encode_operand(&mut self, operand: &Operand<'tcx>) -> Expr {
        match operand {
            Operand::Constant(box cst) => Expr::Lit(self.encode_constant(cst)),
            Operand::Move(place) => self.push_place_read(place, false),
            Operand::Copy(place) => self.push_place_read(place, true),
        }
    }

    pub fn encode_constant(&self, constant: &mir::Constant<'tcx>) -> Literal {
        match constant.literal {
            ConstantKind::Ty(cst) => self.encode_const(cst),
            _ => fatal!(self, "Cannot encode constant yet! {:#?}", constant),
        }
    }

    pub fn encode_const(&self, cst: &Const<'tcx>) -> Literal {
        let cst = self.ty_ctxt.lift(cst).unwrap();
        match cst {
            Const {
                val: ConstKind::Value(v),
                ty,
            } => self.encode_value(v, ty),

            _ => fatal!(self, "Cannot encode const yet! {:#?}", cst),
        }
    }

    pub fn encode_value(&self, val: &ConstValue<'tcx>, ty: Ty<'tcx>) -> Literal {
        match val {
            ConstValue::Scalar(Scalar::Int(scalar_int)) => {
                let x: i64 = scalar_int
                    .to_bits(scalar_int.size())
                    .unwrap()
                    .try_into()
                    .unwrap();
                Literal::Int(x)
            }
            ConstValue::ByRef {
                alloc: _,
                offset: _,
            } => match ty.kind() {
                TyKind::Tuple(..) if !ty.potentially_has_param_types_or_consts() => {
                    let contents = self
                        .ty_ctxt
                        .destructure_const(ty::ParamEnv::reveal_all().and(self.ty_ctxt.mk_const(
                            ty::Const {
                                val: ty::ConstKind::Value(*val),
                                ty,
                            },
                        )));
                    let fields: Vec<Literal> = contents
                        .fields
                        .iter()
                        .copied()
                        .map(|x| self.encode_const(x))
                        .collect();
                    // let mut curr_offset = offset;
                    fields.into()
                }
                _ => fatal!(self, "Cannot encode ByRef value yet"),
            },
            _ => fatal!(self, "Cannot encode value yet: {:#?}", val),
        }
    }

    /// ty has to be a tuple, otherwise, this will panic!
    // pub fn encode_tuple_alloc(&self, _alloc: &Allocation, _ty: Ty<'tcx>) -> Expr {
    //     Expr::undefined()
    // }

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
