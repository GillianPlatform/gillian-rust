use super::memory::MemoryAction;
use crate::codegen::runtime;
use crate::prelude::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::ty::{
    self, adjustment::PointerCast, AdtKind, Const, ConstKind, IntTy::*, ParamEnv, TypeFoldable,
    UintTy::*,
};

macro_rules! extract_int {
    ($self: ident, $c: expr, $ty: expr, $t: ty, $n: expr) => {{
        let i = <$t>::from_be_bytes(
            $c.try_eval_bits($self.tcx, ParamEnv::reveal_all(), $ty)
                .unwrap()
                .to_be_bytes()[(16 - $n)..]
                .try_into()
                .expect("Unreachable"),
        );
        log::debug!("GOT HERE FOR VALUE: {:#?}", i);
        Literal::Int(i as i128)
    }};
}

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
                    enum_typ: self.place_ty(place).ty,
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
                                vec![element_pointer, i.try_to_machine_usize(self.tcx).unwrap().into()].into()
                            },
                            (a, b) => fatal!(
                                self,
                                "Unsizing something that is not an array to slice! Casting {:#?} to {:#?}",
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
            CastKind::Misc => {
                let opty = self.operand_ty(op);
                match (opty.kind(), ty_to.kind()) {
                    (
                        TyKind::RawPtr(ty::TypeAndMut { ty, .. }),
                        TyKind::RawPtr(ty::TypeAndMut { ty: typ, .. }),
                    )
                    | (TyKind::Ref(_, ty, _), TyKind::Ref(_, typ, _)) => {
                        self.encode_simple_ptr_cast(enc_op, ty, typ)
                    }
                    _ => fatal!(self, "Cannot encode cast from {:#?} to {:#?}", opty, ty_to),
                }
            }
            CastKind::Pointer(k) => fatal!(
                self,
                "Cannot encode this kind of pointer cast yet: {:#?}, from {:#?} to {:#?}",
                k,
                self.operand_ty(op),
                ty_to
            ),
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
                let max_val = left_ty.numeric_max_val(self.tcx).unwrap();
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
        let cst = self.tcx.lift(cst).unwrap();

        match cst {
            Const {
                val: ConstKind::Value(v),
                ty,
            } => match ty.kind() {
                TyKind::Int(I128) => {
                    extract_int!(self, cst, ty, i128, 16)
                }
                TyKind::Int(I64) => {
                    extract_int!(self, cst, ty, i64, 8)
                }
                TyKind::Int(I32) => {
                    extract_int!(self, cst, ty, i32, 4)
                }
                TyKind::Int(I16) => {
                    extract_int!(self, cst, ty, i32, 2)
                }
                TyKind::Int(I8) => {
                    extract_int!(self, cst, ty, i32, 1)
                }
                TyKind::Int(Isize) => {
                    extract_int!(self, cst, ty, isize, std::mem::size_of::<isize>())
                }
                TyKind::Uint(U128) => fatal!(self, "Cannot handle u128"),
                TyKind::Uint(..) => {
                    let i = cst
                        .try_eval_bits(self.tcx, ParamEnv::reveal_all(), ty)
                        .unwrap() as i128;
                    Literal::Int(i)
                }
                _ => self.encode_value(v, ty), // This should be replaced here, it's not really useful anymore
            },
            // Const {
            //     val: ConstKind::Unevaluated(uneval),
            //     ty,
            // } => {
            //     let v = self
            //         .tcx
            //         .const_eval_resolve(ParamEnv::reveal_all(), *uneval, None)
            //         .expect("Unevaluated cannot be resolved");
            //     self.encode_value(&v, ty)
            // }
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
            ConstValue::ByRef {
                alloc: _,
                offset: _,
            } => match ty.kind() {
                TyKind::Tuple(..) if !ty.potentially_has_param_types_or_consts() => {
                    let contents = self.tcx.destructure_const(ty::ParamEnv::reveal_all().and(
                        self.tcx.mk_const(ty::Const {
                            val: ty::ConstKind::Value(*val),
                            ty,
                        }),
                    ));
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
}
