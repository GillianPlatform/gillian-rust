use gillian::gil::Pred;

use crate::prelude::*;
use crate::utils::attrs::*;

#[derive(Debug)]
pub enum LogicItem {
    Pred(Pred),
}

fn compile_abstract_predicate(tcx: TyCtxt, def_id: DefId) -> Pred {
    let sig = tcx.fn_sig(def_id);
    let inputs = sig.inputs();
    let pred_name = tcx.def_path_str(def_id);
    if !inputs.bound_vars().is_empty() {
        tcx.sess
            .fatal("Predicate signature as bound regions or variables")
    };
    let mut ins = vec![];
    let mut params = vec![];
    let facts = vec![]; // We should add type info in here.
    for (i, ty) in inputs.skip_binder().iter().enumerate() {
        params.push((format!("pred_arg{}", i), None));
        if let TyKind::Adt(def, _) = ty.kind() {
            if tcx.is_diagnostic_item(Symbol::intern("gillian::predicate::in"), def.did()) {
                ins.push(i)
            }
        }
    }
    Pred {
        name: pred_name,
        num_params: params.len(),
        params,
        abstract_: true,
        facts,
        definitions: vec![],
        ins,
        pure: false,
    }
}

pub fn compile_logic(tcx: TyCtxt, def_id: DefId) -> LogicItem {
    if is_abstract_predicate(tcx, def_id) {
        let pred = compile_abstract_predicate(tcx, def_id);
        println!("{}", &pred);
        return LogicItem::Pred(pred);
    }
    unreachable!()
}
