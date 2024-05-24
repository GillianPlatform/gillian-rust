use super::attrs::{is_logic, should_translate};
use crate::prelude::*;
use rustc_index::IndexVec;

pub(crate) fn make_loop(_: TyCtxt) -> IndexVec<BasicBlock, BasicBlockData> {
    let mut body = IndexVec::new();
    body.push(BasicBlockData::new(Some(Terminator {
        source_info: SourceInfo::outermost(rustc_span::DUMMY_SP),
        kind: TerminatorKind::Return,
    })));
    body
}

pub(crate) fn cleanup_logic<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, body: &mut Body<'tcx>) {
    if is_logic(def_id, tcx) || !should_translate(def_id, tcx) {
        log::trace!("replacing function body for {:?}", def_id);
        *body.basic_blocks_mut() = make_loop(tcx);
        body.var_debug_info = Vec::new();
    };
}
