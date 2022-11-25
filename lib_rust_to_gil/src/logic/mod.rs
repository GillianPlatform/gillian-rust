use gillian::gil::Pred;

use crate::prelude::*;
use crate::utils::attrs::*;

mod builtins;
mod predicate;

#[derive(Debug)]
pub enum LogicItem {
    Pred(Pred),
}

pub fn compile_logic(tcx: TyCtxt, did: DefId) -> LogicItem {
    if is_abstract_predicate(tcx, did) {
        let pred = predicate::PredCtx::new(tcx, did, true).compile();
        println!("{}", &pred);
        return LogicItem::Pred(pred);
    }
    if is_predicate(tcx, did) {
        let pred = predicate::PredCtx::new(tcx, did, false).compile();
        println!("{}", &pred);
        return LogicItem::Pred(pred);
    }
    unreachable!()
}
