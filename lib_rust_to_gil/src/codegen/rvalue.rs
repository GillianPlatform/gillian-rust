use super::memory::MemoryAction;
use super::place::GilPlace;
use crate::codegen::runtime;
use crate::prelude::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::ty::{self, adjustment::PointerCast, AdtKind, Const, ConstKind};

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn push_encode_rvalue(&mut self, rvalue: &Rvalue<'tcx>) -> Expr {
        match rvalue {
            Rvalue::Use(operand) => self.push_encode_operand(operand),
            Rvalue::BinaryOp(binop, box (left, right))
            | Rvalue::CheckedBinaryOp(binop, box (left, right)) => {
                self.push_encode_binop(binop, left, right)
            }
            &Rvalue::Ref(_region, _, place) => {
                // I need to know how to handle the BorrowKind
                // I don't know what needs to be done, maybe nothing
                // Polonius will come into the game here.
                if matches!(
                    self.rvalue_ty(rvalue).kind(),
                    TyKind::Ref(_, _, Mutability::Mut)
                ) {
                    // The case of mutable references, what do we do with the prophecy?
                    if place.projection.len() == 1 && place.projection[0] == PlaceElem::Deref {
                        // FIXME: HACK
                        // This assumes that the lifetime of th created reference is the same as the old one,
                        // since we carry the exact same prophecy around. It is not correct in general.
                        let local = Expr::PVar(self.name_from_local(place.local));
                        self.push_read_gil_place(
                            GilPlace::base(local, self.place_ty(place).ty),
                            self.rvalue_ty(rvalue),
                            true,
                        )
                    } else {
                        let gil_place = self.push_get_gil_place(place);
                        let prophecy = self.push_create_prophecy_for(place);
                        [gil_place.into_expr_ptr(), prophecy].into()
                    }
                } else {
                    let gil_place = self.push_get_gil_place(place);
                    gil_place.into_expr_ptr()
                }
            }
            &Rvalue::AddressOf(_, place) => {
                let gil_place = self.push_get_gil_place(place);
                gil_place.into_expr_ptr()
            }
            &Rvalue::Discriminant(place) => {
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
            &Rvalue::Len(place) => {
                let expr = self.push_place_read(place, true);
                expr.lst_len()
            }
            Rvalue::Aggregate(box kind, ops) => {
                let ops: Vec<Expr> = ops.iter().map(|op| self.push_encode_operand(op)).collect();
                let ops: Expr = ops.into();
                match kind {
                    AggregateKind::Array(..) => ops,
                    AggregateKind::Adt(
                        adt_did,
                        variant_idx,
                        _subst,
                        _type_annot,
                        _active_field,
                    ) => {
                        let def = self.tcx().adt_def(adt_did);
                        match def.adt_kind() {
                            AdtKind::Enum => {
                                let n: Expr = variant_idx.as_u32().into();
                                vec![n, ops].into()
                            }
                            AdtKind::Struct => ops,
                            AdtKind::Union => {
                                fatal!(self, "Union aggregate expressions not handeld yet")
                            }
                        }
                    }
                    AggregateKind::Tuple => ops,
                    _ => panic!("Unhandled agregate kind: {:#?}", kind),
                }
            }
            Rvalue::Cast(ckind, op, ty_to) => self.push_encode_cast(ckind, op, *ty_to),
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
                           (TyKind::Array(element_ty , cst), TyKind::Slice(..)) => {
                                let vtsz = cst.kind().try_to_value().expect("Array size is not a value");
                                let sz = self.encode_valtree(&vtsz, cst.ty());
                                let element_pointer = self.push_cast_array_to_element_pointer(enc_op, *left, *element_ty);
                                vec![element_pointer, sz.into()].into()
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
            CastKind::PtrToPtr => {
                let opty = self.operand_ty(op);
                match (opty.kind(), ty_to.kind()) {
                    (
                        TyKind::RawPtr(ty::TypeAndMut { ty, .. }),
                        TyKind::RawPtr(ty::TypeAndMut { ty: typ, .. }),
                    ) if matches!(ty.kind(), TyKind::Slice(..))
                        && !matches!(typ.kind(), TyKind::Slice(..)) =>
                    {
                        Expr::lnth(enc_op, 0)
                    }
                    (
                        TyKind::RawPtr(ty::TypeAndMut { ty, .. }),
                        TyKind::RawPtr(ty::TypeAndMut { ty: typ, .. }),
                    )
                    | (TyKind::Ref(_, ty, _), TyKind::Ref(_, typ, _)) => {
                        log::debug!(
                            "Encoding cast from *{:#?} to *{:#?} as simple cast!",
                            ty,
                            typ
                        );
                        self.encode_simple_ptr_cast(enc_op, *ty, *typ)
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
            CastKind::FnPtrToPtr
            | CastKind::IntToInt
            | CastKind::PointerExposeAddress
            | CastKind::PointerFromExposedAddress
            | CastKind::DynStar
            | CastKind::FloatToFloat
            | CastKind::FloatToInt
            | CastKind::IntToFloat => fatal!(
                self,
                "Cannot encode PointerExposeAddress and PointerFromExposedAddress yet"
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
        use mir::BinOp::*;
        match binop {
            Add if left_ty.is_integral() && left_ty == right_ty => {
                let max_val = left_ty.numeric_max_val(self.tcx()).unwrap();
                let max_val = self.encode_const(&max_val);
                let temp = self.temp_var();
                self.push_cmd(runtime::checked_add(
                    temp.clone(),
                    e1,
                    e2,
                    Expr::Lit(max_val),
                ));
                Expr::PVar(temp)
            }
            Sub if left_ty.is_integral() && left_ty == right_ty => {
                // TODO: add bound checks
                let temp = self.temp_var();
                self.push_cmd(runtime::checked_sub(temp.clone(), e1, e2));
                Expr::PVar(temp)
            }
            Gt if left_ty.is_numeric() && left_ty == right_ty => {
                if left_ty.is_integral() {
                    Expr::i_gt(e1, e2)
                } else {
                    Expr::f_gt(e1, e2)
                }
            }
            Lt if left_ty.is_numeric() && left_ty == right_ty => {
                if left_ty.is_integral() {
                    Expr::i_lt(e1, e2)
                } else {
                    Expr::f_lt(e1, e2)
                }
            }
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
            Operand::Move(place) => self.push_place_read(*place, false),
            Operand::Copy(place) => self.push_place_read(*place, true),
        }
    }

    pub fn encode_constant(&self, constant: &mir::Constant<'tcx>) -> Literal {
        self.encode_constant_kind(&constant.literal)
    }

    pub fn encode_constant_kind(&self, ckind: &mir::ConstantKind<'tcx>) -> Literal {
        match ckind {
            ConstantKind::Ty(cst) => self.encode_const(cst),
            ConstantKind::Val(val, ty) => self.encode_value(val, *ty),
            ConstantKind::Unevaluated(..) => fatal!(self, "Can't encode unevaluated constants yet"),
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
                TyKind::Tuple(..) => {
                    let contents = self.tcx().destructure_mir_constant(
                        ty::ParamEnv::reveal_all(),
                        ConstantKind::Val(*val, ty),
                    );
                    let fields: Vec<Literal> = contents
                        .fields
                        .iter()
                        .map(|x| self.encode_constant_kind(x))
                        .collect();
                    // let mut curr_offset = offset;
                    fields.into()
                }
                _ => fatal!(self, "Cannot encode ByRef value yet"),
            },
            ConstValue::Scalar(Scalar::Int(scalar_int)) => {
                self.encode_valtree(&ValTree::Leaf(*scalar_int), ty)
            }
            ConstValue::ZeroSized => self.zst_value_of_type(ty),
            _ => fatal!(self, "Cannot encode value yet: {:#?}", val),
        }
    }

    pub fn encode_const(&self, cst: &Const<'tcx>) -> Literal {
        match cst.kind() {
            ConstKind::Value(vt) => self.encode_valtree(&vt, cst.ty()),
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
            TyKind::Tuple(_) if ty.tuple_fields().iter().next().is_none() => vec![].into(),
            _ => fatal!(self, "Cannot encode zst of type {:#?} yet", ty),
        }
    }

    pub fn encode_valtree(&self, vt: &ValTree<'tcx>, ty: Ty<'tcx>) -> Literal {
        if Self::valtree_is_zst(vt) {
            return self.zst_value_of_type(ty);
        };
        match (vt, ty.kind()) {
            (ValTree::Leaf(scalar_int), TyKind::Uint(..)) => {
                let u = scalar_int
                    .try_to_uint(scalar_int.size())
                    .expect("cannot fail because we chose the right size");
                Literal::int(u)
            }
            (ValTree::Leaf(scalar_int), TyKind::Int(..)) => {
                let i = scalar_int
                    .try_to_int(scalar_int.size())
                    .expect("cannot fail because we chose the right size");
                Literal::int(i)
            }
            (ValTree::Leaf(..), _) => {
                fatal!(self, "Invalid ty for ValTree Leaf: {:?}", ty)
            }
            (ValTree::Branch(slice), TyKind::Tuple(..)) => Literal::LList(
                slice
                    .iter()
                    .zip(ty.tuple_fields())
                    .map(|(nvt, nty)| self.encode_valtree(nvt, nty))
                    .collect(),
            ),
            _ => {
                fatal!(self, "Cannot encode valtree {:?} with type {:?}", vt, ty)
            }
        }
    }
}
