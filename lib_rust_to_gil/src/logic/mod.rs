use std::collections::HashMap;

use gillian::gil::Pred;

use crate::prelude::*;
use crate::utils::attrs::*;
use crate::utils::polymorphism::{HasGenericArguments, HasGenericLifetimes};

mod builtins;
mod core_preds;
mod dummy_pre;
mod lemma;
mod predicate;
mod traits;
mod utils;

#[derive(Debug)]
pub enum LogicItem {
    Pred(Pred),
    Lemma(Lemma),
    Precondition(Symbol, Vec<String>, Assertion),
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
    } else if is_lemma(did, tcx) {
        let lemma =
            lemma::LemmaCtx::new(tcx, global_env, did, is_trusted_lemma(did, tcx)).compile();
        LogicItem::Lemma(lemma)
    } else if is_precondition(did, tcx) {
        log::debug!("Compiling precondition: {:?}", did);
        let pred_ctx = predicate::PredCtx::new(tcx, global_env, did, false);
        let generic_amounts = pred_ctx.generic_types().len() + pred_ctx.generic_lifetimes().len();
        let mut pred = pred_ctx.compile();
        assert!(
            pred.definitions.len() == 1,
            "precondition must have exactly one definition"
        );
        let id = tcx
            .get_diagnostic_name(did)
            .expect("All preconditions should be diagnostic items");
        let mut definition = pred.definitions.pop().unwrap();
        for (name, _) in pred.params.iter().take(generic_amounts) {
            let lvar_name = format!("#{}", name.clone());
            definition = Assertion::star(
                Assertion::Pure(Formula::eq(Expr::PVar(name.clone()), Expr::LVar(lvar_name))),
                definition,
            )
        }
        let args = std::mem::take(&mut pred.params)
            .into_iter()
            .map(|p| p.0)
            .collect();
        LogicItem::Precondition(id, args, definition)
        // Has to b safe, because we know there is exactly one definition
    } else if is_postcondition(did, tcx) {
        let pred_ctx = predicate::PredCtx::new(tcx, global_env, did, false);
        let ty_amount = pred_ctx.generic_types().len();
        let mut pred = pred_ctx.compile();
        let mut map = HashMap::new();
        for (name, _) in pred.params.iter().take(ty_amount) {
            map.insert(name.clone(), Expr::LVar(format!("#{}", &name)));
        }
        assert!(
            pred.definitions.len() == 1,
            "postconditions must have exactly one definition"
        );
        let mut assertion = pred.definitions.pop().unwrap();
        assertion.subst_pvar(&map);
        let id = tcx
            .get_diagnostic_name(did)
            .expect("All postcondition should be diagnostic items");
        LogicItem::Postcondition(id, assertion)
        // Has to b safe, because we know there is exactly one definition
    } else {
        unreachable!()
    }
}

pub fn dummy_pre(tcx: TyCtxt, did: DefId) -> gillian::gil::Assertion {
    dummy_pre::DummyPre::new(did, tcx).into()
}
