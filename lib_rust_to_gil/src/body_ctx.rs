use super::names::{ret_var, temp_name_from_local, gil_temp_from_id};
use rustc_index::vec::IndexVec;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::{ConstKind};
use rustc_target::abi::Size;

pub struct BodyCtxt<'gil, 'tcx> {
    var_debug_info: &'gil Vec<VarDebugInfo<'tcx>>,
    source_scopes: &'gil IndexVec<SourceScope, SourceScopeData<'tcx>>,
    pub(crate) ty_ctxt: &'gil TyCtxt<'tcx>,
    gil_temp_counter: u32,
}

impl<'gil, 'tcx> BodyCtxt<'gil, 'tcx> {
    pub fn new(body: &'tcx Body, ty_ctxt: &'gil TyCtxt<'tcx>) -> Self {
        BodyCtxt {
            var_debug_info: &body.var_debug_info,
            source_scopes: &body.source_scopes,
            ty_ctxt,
            gil_temp_counter: 0,
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
    
    pub fn temp_var(&mut self) -> String {
        let current = self.gil_temp_counter;
        self.gil_temp_counter += 1;
        gil_temp_from_id(current)
    } 
}
