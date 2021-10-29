use super::names::{gil_temp_from_id, ret_var, temp_name_from_local};
use crate::prelude::*;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::ty::ConstKind;
use rustc_target::abi::Size;

pub struct BodyCtxt<'tcx> {
    pub(crate) instance: Instance<'tcx>,
    pub(crate) ty_ctxt: TyCtxt<'tcx>,
    gil_temp_counter: u32,
}

impl<'tcx> BodyCtxt<'tcx> {
    pub fn new(instance: Instance<'tcx>, ty_ctxt: TyCtxt<'tcx>) -> Self {
        BodyCtxt {
            instance,
            ty_ctxt,
            gil_temp_counter: 0,
        }
    }

    pub fn mir(&self) -> &'tcx Body<'tcx> {
        self.ty_ctxt.instance_mir(self.instance.def)
    }

    pub fn _location(&self, scope: &SourceScope) {
        let _source = self.mir().source_scopes.get(*scope);
    }

    pub fn original_name_from_local(&self, local: &Local) -> Option<String> {
        self.mir()
            .var_debug_info
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

    pub fn temp_var(&mut self) -> String {
        let current = self.gil_temp_counter;
        self.gil_temp_counter += 1;
        gil_temp_from_id(current)
    }
}
