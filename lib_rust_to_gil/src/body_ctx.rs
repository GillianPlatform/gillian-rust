use super::names::ret_var;
use rustc_index::vec::IndexVec;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;

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
                None => String::from("gvar") + &local.as_u32().to_string(),
            }
        }
    }
}
