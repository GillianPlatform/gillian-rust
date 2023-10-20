use std::collections::HashMap;

use gillian::gil::Pred;

use crate::prelude::*;
use crate::temp_gen::TempGenerator;
use crate::utils::attrs::*;
use crate::utils::polymorphism::HasGenericArguments;

pub(crate) mod builtins;
pub(crate) mod core_preds;
mod dummy_pre;
mod extract_lemma_utils;
mod lemma;
pub(crate) mod param_collector;
mod predicate;
pub(crate) mod traits;
mod utils;

pub(crate) use predicate::PredCtx;

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
        lemma::LemmaCtx::new(
            global_env,
            did,
            temp_gen,
            is_trusted_lemma(did, tcx),
            is_extract_lemma(did, tcx),
        )
        .compile()
    } else if is_precondition(did, tcx) {
        log::debug!("Compiling precondition: {:?}", did);
        let pred_ctx = predicate::PredCtx::new_with_identity_args(global_env, temp_gen, did);
        let generic_amounts =
            pred_ctx.generic_types().len() + (pred_ctx.has_generic_lifetimes() as usize);
        let mut pred = pred_ctx.compile_concrete();
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
                Expr::PVar(name.clone()).eq_f(Expr::LVar(lvar_name)).into(),
                definition,
            )
        }
        let args = std::mem::take(&mut pred.params)
            .into_iter()
            .map(|p| p.0)
            .collect();
        vec![LogicItem::Precondition(id, args, definition)]
        // Has to b safe, because we know there is exactly one definition
    } else if is_postcondition(did, tcx) {
        log::debug!("Compiling postcondition: {:?}", did);
        let pred_ctx = predicate::PredCtx::new_with_identity_args(global_env, temp_gen, did);
        let generics_amount =
            pred_ctx.generic_types().len() + (pred_ctx.has_generic_lifetimes() as usize);
        let mut pred = pred_ctx.compile_concrete();
        let mut map = HashMap::new();
        for (name, _) in pred.params.iter().take(generics_amount) {
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
        vec![LogicItem::Postcondition(id, assertion)]
        // Has to b safe, because we know there is exactly one definition
    } else if is_fold(did, tcx) || is_unfold(did, tcx) {
        vec![]
    } else {
        unreachable!()
    }
}

pub fn dummy_pre(tcx: TyCtxt, did: DefId) -> gillian::gil::Assertion {
    dummy_pre::DummyPre::new(did, tcx).into()
}
