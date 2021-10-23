use crate::body_ctx::BodyCtxt;
use gillian::gil::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::Constant as MirConstant;
use rustc_middle::mir::*;
use rustc_middle::ty::{Const, ConstKind};
use std::convert::TryInto;

impl<'gil, 'tcx> BodyCtxt<'gil, 'tcx> {
    pub fn compile_rvalue(&self, rvalue: &Rvalue<'tcx>) -> Expr {
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
}
