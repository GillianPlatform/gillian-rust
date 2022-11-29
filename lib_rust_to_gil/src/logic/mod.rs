use gillian::gil::Pred;

use crate::prelude::*;
use crate::utils::attrs::*;

mod builtins;
mod core_preds;
mod predicate;

#[derive(Debug)]
pub enum LogicItem {
    Pred(Pred),
}

pub fn compile_logic<'tcx, 'genv>(
    did: DefId,
    tcx: TyCtxt<'tcx>,
    global_env: &'genv mut GlobalEnv<'tcx>,
) -> LogicItem {
    if is_abstract_predicate(did, tcx) {
        let pred = predicate::PredCtx::new(tcx, global_env, did, true).compile();
        println!("{}", &pred);
        return LogicItem::Pred(pred);
    }
    if is_predicate(did, tcx) {
        let pred = predicate::PredCtx::new(tcx, global_env, did, false).compile();
        println!("{}", &pred);
        return LogicItem::Pred(pred);
    }
    unreachable!()
}
