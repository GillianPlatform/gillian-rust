use gillian::gil::Pred;

use crate::prelude::*;
use crate::utils::attrs::*;

mod builtins;
mod core_preds;
mod predicate;

#[derive(Debug)]
pub enum LogicItem {
    Pred(Pred),
    Precondition(Symbol, Assertion),
    Postcondition(Symbol, Assertion),
}

pub fn compile_logic<'tcx, 'genv>(
    did: DefId,
    tcx: TyCtxt<'tcx>,
    global_env: &'genv mut GlobalEnv<'tcx>,
) -> LogicItem {
    if is_abstract_predicate(did, tcx) {
        let pred = predicate::PredCtx::new(tcx, global_env, did, true).compile();
        LogicItem::Pred(pred)
    } else if is_predicate(did, tcx) {
        let pred = predicate::PredCtx::new(tcx, global_env, did, false).compile();
        LogicItem::Pred(pred)
    } else if is_precondition(did, tcx) {
        let mut pred = predicate::PredCtx::new(tcx, global_env, did, false).compile();
        assert!(
            pred.definitions.len() == 1,
            "precondition must have exactly one definition"
        );
        let id = tcx
            .get_diagnostic_name(did)
            .expect("All preconditions should be diagnostic items");
        LogicItem::Precondition(id, pred.definitions.pop().unwrap())
        // Has to b safe, because we know there is exactly one definition
    } else if is_postcondition(did, tcx) {
        let mut pred = predicate::PredCtx::new(tcx, global_env, did, false).compile();
        assert!(
            pred.definitions.len() == 1,
            "postconditions must have exactly one definition"
        );
        let id = tcx
            .get_diagnostic_name(did)
            .expect("All postcondition should be diagnostic items");
        LogicItem::Postcondition(id, pred.definitions.pop().unwrap())
        // Has to b safe, because we know there is exactly one definition
    } else {
        unreachable!()
    }
}
