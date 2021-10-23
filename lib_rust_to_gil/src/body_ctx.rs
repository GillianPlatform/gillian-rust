use super::names::{ret_var, temp_name_from_local};
use rustc_index::vec::IndexVec;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::Constant as MirConstant;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::{Const, ConstKind, TyKind};
use rustc_target::abi::Size;

pub struct BodyCtxt<'gil, 'tcx> {
    var_debug_info: &'gil Vec<VarDebugInfo<'tcx>>,
    source_scopes: &'gil IndexVec<SourceScope, SourceScopeData<'tcx>>,
    ty_ctxt: &'gil TyCtxt<'tcx>,
}

impl<'gil, 'tcx> BodyCtxt<'gil, 'tcx> {
    pub fn new(body: &'tcx Body, ty_ctxt: &'gil TyCtxt<'tcx>) -> Self {
        BodyCtxt {
            var_debug_info: &body.var_debug_info,
            source_scopes: &body.source_scopes,
            ty_ctxt,
        }
    }

    pub fn location(&self, scope: &SourceScope) {
        let _source = self.source_scopes.get(*scope);
    }

    pub fn original_name_from_local(&self, local: &Local) -> Option<String> {
        self.var_debug_info
            .iter()
            .find_map(|debug_info| match debug_info.value {
                VarDebugInfoContents::Place(place)
                    if place.local == *local && place.projection.is_empty() =>
                {
                    Some(debug_info.name.to_string())
                }
                _ => None,
            })
    }

    pub fn name_from_local(&self, local: &Local) -> String {
        if *local == RETURN_PLACE {
            ret_var()
        } else {
            match self.original_name_from_local(local) {
                Some(name) => name,
                None => temp_name_from_local(local),
            }
        }
    }

    pub fn is_zst(val: &ConstKind) -> bool {
        match val {
            ConstKind::Value(ConstValue::Scalar(Scalar::Int(sci))) => sci.size() == Size::ZERO,
            _ => false,
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
