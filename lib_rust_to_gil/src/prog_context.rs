use std::rc::Rc;
use std::str::FromStr;

use polonius_engine::{Algorithm, Output};

use super::temp_gen::TempGenerator;
use crate::config::Config;
use crate::location_table::LocationTable;
use crate::logic::{compile_logic, LogicItem};
use crate::prelude::*;
use crate::signature::build_signature;

pub struct ProgCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    prog: gillian::gil::Prog,
    global_env: GlobalEnv<'tcx>,
    temp_gen: TempGenerator,
}

impl<'tcx> HasTyCtxt<'tcx> for ProgCtx<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx> ProgCtx<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, config: Config) -> Self {
        Self {
            prog: gillian::gil::Prog::new(runtime::imports(config.prophecies)),
            global_env: GlobalEnv::new(tcx, config),
            temp_gen: TempGenerator::new(),
            tcx,
        }
    }

    fn compile_logic(&mut self, did: DefId) {
        for logic_item in compile_logic(did, self.tcx(), &mut self.global_env, &mut self.temp_gen) {
            match logic_item {
                LogicItem::Pred(pred) => self.prog.add_pred(pred),
                LogicItem::Lemma(lemma) => self.prog.add_lemma(lemma),
            }
        }
    }

    fn compile_fn(&mut self, did: DefId) {
        let sig = build_signature(&mut self.global_env, did);
        let with_facts = self.global_env.body_with_facts(did.expect_local());
        let body = with_facts.body.clone();
        let borrow_set = with_facts.borrow_set.clone();
        let region_ctxt = with_facts.region_inference_context.clone();
        let location_table = LocationTable::new(&body);
        let output_facts = {
            let algorithm = Algorithm::from_str("Hybrid").unwrap();
            let input_facts = with_facts.input_facts.clone().unwrap();
            Rc::new(Output::compute(&*input_facts, algorithm, true))
        };
        let ctx = GilCtxt::new(
            &mut self.global_env,
            &body,
            &borrow_set,
            &region_ctxt,
            output_facts,
            location_table,
        );

        let mut proc = ctx.push_body();

        proc.spec = sig.to_gil_spec(&mut self.global_env, proc.name.clone());
        self.prog.add_proc(proc);
    }

    fn final_prog(mut self) -> ParsingUnit {
        for key in self.tcx().hir().body_owners() {
            let did = key.to_def_id();
            if crate::utils::attrs::should_translate(did, self.tcx()) {
                if crate::utils::attrs::is_logic(did, self.tcx()) {
                    self.compile_logic(did);
                } else {
                    self.compile_fn(did);
                }
            }
        }

        self.global_env.flush_remaining_defs_to_prog(&mut self.prog);
        let init_data = self.global_env.serialized_adt_declarations();
        ParsingUnit {
            prog: self.prog,
            init_data,
        }
    }

    pub(crate) fn compile_prog(tcx: TyCtxt<'tcx>, config: Config) -> ParsingUnit {
        let this = Self::new(tcx, config);
        this.final_prog()
    }
}
