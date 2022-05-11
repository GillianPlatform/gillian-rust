use crate::prelude::*;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_hir::definitions::{DefPathData, DisambiguatedDefPathData};
use rustc_span::symbol::sym;

macro_rules! disamb {
    ($p: pat) => {
        DisambiguatedDefPathData { data: $p, .. }
    };
}

impl<'tcx, 'body> GilCtxt<'tcx, 'body> {
    fn is_core(&self, krate: CrateNum) -> bool {
        matches!(self.ty_ctxt.crate_name(krate), sym::core)
    }
    pub(crate) fn shim_with(&self, def_id: DefId) -> Option<String> {
        // We only have shims for core for now
        if !self.is_core(def_id.krate) {
            return None;
        }

        let path = self.ty_ctxt.def_path(def_id);

        use DefPathData::*;

        // Slice shims
        if let Some(disamb!(TypeNs(sym::slice))) = path.data.get(0) {
            if matches!(path.data[1..], [disamb!(Impl), disamb!(ValueNs(sym::len))]) {
                return Some(runtime::slice::SLICE_LEN.to_string());
            }
            return None;
        }
        None
    }
}
