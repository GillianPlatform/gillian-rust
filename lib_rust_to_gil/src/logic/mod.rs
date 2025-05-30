use gillian::gil::Pred;

use crate::prelude::*;
use crate::temp_gen::TempGenerator;
use crate::utils::attrs::*;

pub(crate) mod builtins;
pub(crate) mod core_preds;
pub mod gilsonite;
mod lemma;
pub(crate) mod param_collector;
mod predicate;
pub(crate) mod traits;
pub mod utils;

pub(crate) use lemma::LemmaCtx;
pub(crate) use predicate::PredCtx;

#[derive(Debug)]
pub enum LogicItem {
    Pred(Pred),
    Lemma(Lemma),
}

pub fn compile_logic<'tcx, 'genv>(
    did: DefId,
    tcx: TyCtxt<'tcx>,
    global_env: &'genv mut GlobalEnv<'tcx>,
    temp_gen: &'genv mut TempGenerator,
) -> Vec<LogicItem> {
    if is_abstract_predicate(did, tcx) {
        let pred = predicate::PredCtx::new_with_identity_args(global_env, temp_gen, did)
            .compile_abstract();
        vec![LogicItem::Pred(pred)]
    } else if is_predicate(did, tcx) {
        let pred = predicate::PredCtx::new_with_identity_args(global_env, temp_gen, did)
            .compile_concrete();

        vec![LogicItem::Pred(pred)]
    } else if is_lemma(did, tcx) {
        let lemma = lemma::LemmaCtx::new(global_env, did, temp_gen, is_trusted(did, tcx)).compile();
        vec![LogicItem::Lemma(lemma)]
        // Has to b safe, because we know there is exactly one definition
    } else if is_fold(did, tcx) || is_unfold(did, tcx) || is_specification(did, tcx) {
        vec![]
    } else {
        unreachable!()
    }
}
