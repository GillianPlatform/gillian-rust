use super::memory::MemoryAction;
use super::place::GilPlace;
use crate::codegen::runtime;
use crate::prelude::*;
use num_bigint::BigInt;
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{self, AdtKind, ConstKind};

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    pub fn int_bounds(&self, ty: Ty<'tcx>) -> (BigInt, BigInt) {
        crate::utils::ty::int_bounds(ty, self.tcx())
    }

    pub fn push_encode_rvalue(&mut self, rvalue: &Rvalue<'tcx>) -> Expr {
        match rvalue {
            Rvalue::Use(operand) => self.push_encode_operand(operand),
            Rvalue::BinaryOp(binop, box (left, right))
            | Rvalue::CheckedBinaryOp(binop, box (left, right)) => {
                self.push_encode_binop(binop, left, right)
            }
            &Rvalue::Ref(_region, bk, place) => {
                // I need to know how to handle the BorrowKind
                // I don't know what needs to be done, maybe nothing
                // Polonius will come into the game here.
                if self.prophecies_enabled() && matches!(bk, BorrowKind::Mut { .. }) {
                    let local_ty = self.place_ty(place.local.into()).ty;
                    if place.projection.len() == 1
                        && place.projection[0] == PlaceElem::Deref
                        && ty_utils::is_mut_ref(local_ty)
                    {
                        // If we're just copying a reference, we want to make sure we don't
                        // create a new prophecy but simply copy it.
                        // We hardcode that case.
                        // Note that, the choice of prophecy has absolutely no impact on soundness.
                        // Any value would be valid, but the wrong value will prevent verification to pass.
                        // So we are taking absolutely no soundness risk in hardcoding some choices here.
                        let cur_gil_place =
                            GilPlace::base(Expr::PVar(self.name_from_local(place.local)), local_ty);
                        let copied = self.temp_var();
                        let cur_typ = self.place_ty_until(place, 0);
                        self.push_read_gil_place_in_memory(
                            copied.clone(),
                            cur_gil_place,
                            cur_typ.ty,
                            true,
                        );
                        // The difference with push_get_gil_place is that push_get_gil_place will only return
                        // the place in memory, and therefore peels the prophecy, returning Expr::PVar(copied).lnth(0)
                        Expr::PVar(copied)
                    } else {
                        // Otherwise we do create new prophecy.
                        let gil_place = self.push_get_gil_place(place);
                        let prophecy = self.push_alloc_prophecy();
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
                let gil_place = self.push_get_gil_place(place);
                let (_loc, _proj, meta) = gil_place.into_loc_proj_meta();
                meta.unwrap_or_else(|| fatal!(self, "Getting len of non-slice!?"))
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
                    _ => fatal!(self, "Unhandled agregate kind: {:#?}", kind),
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
            CastKind::PointerCoercion(PointerCoercion::Unsize) => {
                match (self.operand_ty(op).kind(), ty_to.kind()) {
                    (TyKind::Ref(_, left, _), TyKind::Ref(_, right, _)) => {
                        match (left.kind(), right.kind()) {
                           (TyKind::Array(_element_ty , cst), TyKind::Slice(..)) => {
                                let vtsz = cst.to_valtree();
                                let sz = self.encode_valtree(&vtsz, cst.ty());
                                vec![enc_op, sz.into()].into()
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
            // A pointer cast is basically a no-op
            CastKind::PtrToPtr => enc_op,
            // These two operations do nothing in our semantics.
            // It will lead to some failures, but it's ok, it's sound and it supports a large
            // set of programs.
            CastKind::PointerExposeProvenance | CastKind::PointerWithExposedProvenance => enc_op,
            CastKind::IntToInt => {
                let (low, high) = self.int_bounds(ty_to);
                let low_comp = Formula::ILessEq {
                    left: Box::new(Expr::int(low)),
                    right: Box::new(enc_op.clone()),
                };
                let high_comp = Formula::ILessEq {
                    left: Box::new(enc_op.clone()),
                    right: Box::new(Expr::int(high)),
                };
                let both = low_comp.and(high_comp);
                let asrt = Cmd::Logic(LCmd::Assert(both));
                self.push_cmd(asrt);
                enc_op
            }
            CastKind::PointerCoercion(k) => fatal!(
                self,
                "Cannot encode this kind of pointer cast yet: {:#?}, from {:#?} to {:#?}",
                k,
                self.operand_ty(op),
                ty_to
            ),
            CastKind::FnPtrToPtr
            | CastKind::DynStar
            | CastKind::FloatToFloat
            | CastKind::FloatToInt
            | CastKind::IntToFloat
            | CastKind::Transmute => fatal!(self, "Cannot encode {:?} cast yet", kind),
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
                let max_val = self.encode_ty_const(max_val);
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

            Mul if left_ty.is_integral() && left_ty == right_ty => {
                let temp = self.temp_var();
                self.push_cmd(runtime::checked_mul(temp.clone(), e1, e2));
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
            Le if left_ty.is_numeric() && left_ty == right_ty => {
                if left_ty.is_integral() {
                    Expr::i_le(e1, e2)
                } else {
                    Expr::f_le(e1, e2)
                }
            }
            Shl if left_ty.is_integral() && right_ty.is_integral() => Expr::i_shl(e1, e2),
            Eq if left_ty.is_numeric() && left_ty == right_ty => Expr::eq_expr(e1, e2),
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
            Operand::Constant(box cst) => self.push_encode_constant(cst),
            Operand::Move(place) => self.push_place_read(*place, false),
            Operand::Copy(place) => self.push_place_read(*place, true),
        }
    }

    pub fn push_encode_constant(&mut self, constant: &mir::ConstOperand<'tcx>) -> Expr {
        match constant.const_ {
            Const::Ty(cst) => self.encode_ty_const(cst).into(),
            Const::Val(val, ty) => self.encode_value(val, ty).into(),
            Const::Unevaluated(
                UnevaluatedConst {
                    def,
                    args,
                    promoted,
                },
                ty,
            ) => match promoted {
                None => {
                    let proc_ident = self.tcx().def_path_str_with_args(def, args);
                    let parameters =
                        self.only_param_args_for_fn_call(def, args, &[], constant.ty());
                    let variable = self.temp_var();
                    let fn_call = Cmd::Call {
                        variable: variable.clone(),
                        proc_ident: proc_ident.into(),
                        parameters,
                        error_lab: None,
                        bindings: None,
                    };
                    self.push_cmd(fn_call);
                    Expr::PVar(variable)
                }
                Some(..) => {
                    if crate::utils::ty::is_ref_of_zst(ty, self.tcx()) {
                        return Expr::EList(vec![
                            Literal::Loc("$l_dangling".into()).into(),
                            vec![].into(),
                        ]);
                    }
                    // TODO(xavier): FIXME HACK TODO FIX
                    Expr::null()
                    // fatal!(
                    //     self,
                    //     "Can't encode unevaluated promoted constants yet: {:?} {:?} {:?} {:?}",
                    //     self.tcx().def_path_str_with_args(def, args),
                    //     constant.span,
                    //     promoted,
                    //     ty
                    // )
                }
            },
        }
    }

    pub fn encode_value(&self, val: ConstValue<'tcx>, ty: Ty<'tcx>) -> Literal {
        if Self::const_value_is_zst(val) {
            return self.zst_value_of_type(ty);
        };
        match val {
            ConstValue::Scalar(Scalar::Int(scalar_int)) => {
                self.encode_valtree(&ValTree::Leaf(scalar_int), ty)
            }
            ConstValue::ZeroSized => self.zst_value_of_type(ty),
            ConstValue::Slice { .. } => {
                let bytes = val.try_get_slice_bytes_for_diagnostics(self.tcx());
                Literal::string(String::from_utf8_lossy(bytes.unwrap()))
            }
            _ => fatal!(self, "Cannot encode value yet: {:#?}", val),
        }
    }

    pub fn encode_ty_const(&self, cst: ty::Const<'tcx>) -> Literal {
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
            TyKind::FnDef(did, args) => {
                let name = self.tcx().def_path_str_with_args(did, args);
                // In GIL, function identifiers are strings.
                name.into()
            }
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
