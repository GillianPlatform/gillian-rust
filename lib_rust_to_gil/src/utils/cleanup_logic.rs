use super::attrs::is_logic;
use crate::prelude::*;
use rustc_index::vec::IndexVec;

fn make_loop(_tcx: TyCtxt) -> IndexVec<BasicBlock, BasicBlockData> {
    let mut body = IndexVec::new();
    body.push(BasicBlockData::new(Some(Terminator {
        source_info: SourceInfo::outermost(rustc_span::DUMMY_SP),
        kind: TerminatorKind::Goto {
            target: BasicBlock::from_u32(0),
        },
    })));
    body
}

pub(crate) fn cleanup_logic<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, body: &mut Body<'tcx>) {
    if is_logic(tcx, def_id) {
        log::trace!("replacing function body for {:?}", def_id);
        *body.basic_blocks_mut() = make_loop(tcx);
        body.var_debug_info = Vec::new();
    };
}
