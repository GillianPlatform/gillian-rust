use super::memory::MemoryAction;
use crate::codegen::runtime;
use crate::prelude::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::ty::{self, adjustment::PointerCast, AdtKind, Const, ConstKind, TypeFoldable};

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_encode_rvalue(&mut self, rvalue: &Rvalue<'tcx>) -> Expr {
        match rvalue {
            Rvalue::Use(operand) => self.push_encode_operand(operand),
            Rvalue::BinaryOp(binop, box (left, right))
            | Rvalue::CheckedBinaryOp(binop, box (left, right)) => {
                self.push_encode_binop(binop, left, right)
            }
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                // I need to know how to handle the BorrowKind
                // I don't know what needs to be done, maybe nothing
                let gil_place = self.push_get_gil_place(place);
                gil_place.into_expr_ptr()
            }
            Rvalue::Discriminant(place) => {
                let gp = self.push_get_gil_place(place);
                let target = self.temp_var();
                let (location, projection, meta) = gp.into_loc_proj_meta();
                if meta.is_some() {
                    fatal!(self, "Reading discriminant of a fat pointer!");
                }
                let action = MemoryAction::LoadDiscriminant {
                    location,
                    projection,
                };
                self.push_action(target.clone(), action);
                Expr::PVar(target)
            }
            Rvalue::Len(place) => {
                let expr = self.push_place_read(place, true);
                Expr::lst_len(expr)
            }
            Rvalue::Aggregate(box kind, ops) => {
                let ops: Vec<Expr> = ops.iter().map(|op| self.push_encode_operand(op)).collect();
                let ops: Expr = ops.into();
                match kind {
                    AggregateKind::Array(..) => ops,
                    AggregateKind::Adt(def, variant_idx, _subst, _type_annot, _active_field) => {
                        match def.adt_kind() {
                            AdtKind::Enum => {
                                let name: Expr = self.atd_def_name(def).into();
                                let n: Expr = variant_idx.as_u32().into();
                                let value: Expr = vec![n, ops].into();
                                vec![name, value].into()
                            }
                            AdtKind::Struct => {
                                let name: Expr = self.atd_def_name(def).into();
                                vec![name, ops].into()
                            }
                            AdtKind::Union => {
                                fatal!(self, "Union aggregate expressions not handeld yet")
                            }
                        }
                    }
                    AggregateKind::Tuple => ops,
                    _ => panic!("Unhandled agregate kind: {:#?}", kind),
                }
            }
            Rvalue::Cast(ckind, op, ty_to) => self.push_encode_cast(ckind, op, ty_to),
            _ => fatal!(self, "Unhandled rvalue: {:#?}", rvalue),
        }
    }

    pub fn push_encode_cast(
        &mut self,
        kind: &CastKind,
        op: &Operand<'tcx>,
        ty_to: Ty<'tcx>,
    ) -> Expr {
        let enc_op = self.push_encode_operand(op);
        match kind {
            CastKind::Pointer(PointerCast::Unsize) => {
                match (self.operand_ty(op).kind(), ty_to.kind()) {
                    (TyKind::Ref(_, left, _), TyKind::Ref(_, right, _)) => {
                        match (left.kind(), right.kind()) {
                           (TyKind::Array(element_ty , Const {
                                val: ConstKind::Value(ConstValue::Scalar(Scalar::Int(i))), ..
                            }), TyKind::Slice(..)) => {
                                let element_pointer = self.push_cast_array_to_element_pointer(enc_op, left, element_ty);
                                vec![element_pointer, i.try_to_machine_usize(self.ty_ctxt).unwrap().into()].into()
                            },
                            (a, b) => fatal!(
                                self,
                                "Unsizing something that is not two refs! an array to slice! Casting {:#?} to {:#?}",
                                a,
                                b
                            ),
                        }
                    }
                    (a, b) => fatal!(
                        self,
                        "Unsizing something that is not two refs! Casting {:#?} to {:#?}",
                        a,
                        b
                    ),
                }
            }
            _ => {
                log::warn!("Ignoring misc cast! {:#?} to {:#?}", op, ty_to);
                enc_op
            }
        }
    }

    pub fn push_encode_binop(
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
            mir::BinOp::Gt if left_ty.is_numeric() => {
                let ret = self.temp_var();
                let comp_expr = if left_ty.is_integral() {
                    Expr::i_gt(e1, e2)
                } else {
                    Expr::f_gt(e1, e2)
                };
                self.push_cmd(runtime::int_of_bool(ret.clone(), comp_expr));
                Expr::PVar(ret)
            }
            mir::BinOp::Lt if left_ty.is_numeric() => {
                let ret = self.temp_var();
                let comp_expr = if left_ty.is_integral() {
                    Expr::i_lt(e1, e2)
                } else {
                    Expr::f_lt(e1, e2)
                };
                self.push_cmd(runtime::int_of_bool(ret.clone(), comp_expr));
                Expr::PVar(ret)
            }
            mir::BinOp::Gt | mir::BinOp::Add => fatal!(
                self,
                "Numeric operation on non-numeric values: {:#?} {:#?} and {:#?}",
                binop,
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

    // fn is_zst(si: &ScalarInt<'tcx>) -> bool {
    //     si.size() = Size::ZERO;
    // }

    pub fn zst_value_of_type(&self, ty: Ty<'tcx>) -> Literal {
        match ty.kind() {
            TyKind::Tuple(_) if ty.tuple_fields().next().is_none() => vec![].into(),
            _ => fatal!(self, "Cannot encode zst of type {:#?} yet", ty),
        }
    }

    pub fn encode_value(&self, val: &ConstValue<'tcx>, ty: Ty<'tcx>) -> Literal {
        if Self::const_value_is_zst(val) {
            return self.zst_value_of_type(ty);
        };
        match val {
            ConstValue::Scalar(Scalar::Int(scalar_int)) if ty.is_scalar() => {
                let x = scalar_int.to_bits(scalar_int.size()).unwrap() as i128;
                Literal::Int(x)
            }
            ConstValue::Scalar(Scalar::Int(scalar_int))
                if matches!(
                        ty.kind(),
                        TyKind::Adt(def, _) if def.is_struct()
                ) =>
            {
                // It's a struct with only one field
                let x: i128 = scalar_int
                    .to_bits(scalar_int.size())
                    .unwrap()
                    .try_into()
                    .unwrap();
                vec![Literal::Int(x)].into()
            }
            ConstValue::Scalar(Scalar::Int(scalar_int)) if ty.is_enum() => {
                // It's an enum value with no fields
                let x: i128 = scalar_int
                    .to_bits(scalar_int.size())
                    .unwrap()
                    .try_into()
                    .unwrap();
                vec![Literal::Int(x)].into()
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
            }) if Self::const_is_zst(val) && ty.is_fn() => match ty.kind() {
                TyKind::FnDef(did, _) => match self.shim_with(*did) {
                    Some(s) => s,
                    None => self.ty_ctxt.def_path_str(*did),
                },
                tyk => fatal!(self, "unhandled TyKind for function name: {:#?}", tyk),
            },
            _ => fatal!(
                self,
                "Can't handle dynamic calls yet! Got fun operand: {:#?}",
                operand
            ),
        }
    }
}
