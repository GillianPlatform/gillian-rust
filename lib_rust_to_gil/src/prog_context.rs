use std::rc::Rc;
use std::str::FromStr;

use polonius_engine::{Algorithm, Output};
use rustc_hir::def::DefKind;

use super::temp_gen::TempGenerator;
use crate::config::Config;
use crate::location_table::LocationTable;
use crate::logic::{compile_logic, LogicItem};
use crate::metadata::BinaryMetadata;
use crate::prelude::*;
use crate::signature::build_signature;
use crate::utils::attrs::{is_predicate, is_specification, is_trusted};

pub struct ProgCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    prog: gillian::gil::Prog,
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
            temp_gen: TempGenerator::new(),
            tcx,
        }
    }

    fn compile_logic(&mut self, global_env: &mut GlobalEnv<'tcx>, did: DefId) {
        for logic_item in compile_logic(did, self.tcx(), global_env, &mut self.temp_gen) {
            match logic_item {
                LogicItem::Pred(pred) => self.prog.add_pred(pred),
                LogicItem::Lemma(lemma) => self.prog.add_lemma(lemma),
            }
        }
    }

    fn compile_fn(&mut self, global_env: &mut GlobalEnv<'tcx>, did: DefId) {
        let args = GenericArgs::identity_for_item(self.tcx(), did);

        if is_trusted(did, self.tcx()) {
            let mut temp_gen = TempGenerator::new();
            let sig = build_signature(global_env, did, args, &mut temp_gen);
            let proc_name = self.tcx().def_path_str_with_args(did, args);
            return self
                .prog
                .add_only_spec(sig.to_gil_spec(global_env, proc_name).unwrap());
        };

        let with_facts = global_env.body_with_facts(did.expect_local());
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
            global_env,
            &body,
            &borrow_set,
            &region_ctxt,
            output_facts,
            location_table,
        );

        let mut proc = ctx.push_body();
        if let DefKind::AssocConst = global_env.tcx().def_kind(did) {
            // We can't build signatures for associated consts.
        } else {
            let mut temp_gen = TempGenerator::new();
            let sig = build_signature(global_env, did, args, &mut temp_gen);

            proc.spec = sig.to_gil_spec(global_env, proc.name.clone());
        };
        self.prog.add_proc(proc);
    }

    fn final_prog(&mut self, global_env: &mut GlobalEnv<'tcx>) -> ParsingUnit {
        for key in self.tcx().hir().body_owners() {
            let did = key.to_def_id();
            if self.tcx.def_kind(key) == DefKind::AnonConst {
                continue;
            }

            if crate::utils::attrs::should_translate(did, self.tcx())
            // && !parent_trusted(did, self.tcx())
            {
                if crate::utils::attrs::is_logic(did, self.tcx()) {
                    self.compile_logic(global_env, did);
                } else {
                    self.compile_fn(global_env, did);
                }
            }
        }

        global_env.flush_remaining_defs_to_prog(&mut self.prog);
        let init_data = global_env.serialized_adt_declarations();
        ParsingUnit {
            prog: std::mem::take(&mut self.prog),
            init_data,
        }
    }

    fn only_metadata(&mut self, global_env: &mut GlobalEnv<'tcx>) {
        for key in self.tcx().hir().body_owners() {
            let did = key.to_def_id();
            if self.tcx.def_kind(key) == DefKind::AnonConst {
                continue;
            }

            // For every spec and predicate to be loaded.
            if crate::utils::attrs::should_translate(did, self.tcx())
                && crate::utils::attrs::is_logic(did, self.tcx())
            // && !parent_trusted(did, self.tcx())
            {
                if is_predicate(did, self.tcx()) {
                    global_env.predicate(did);
                }
                if is_specification(did, self.tcx()) {
                    global_env.gilsonite_spec(did);
                }
            }
        }
    }

    pub(crate) fn compile_prog(
        tcx: TyCtxt<'tcx>,
        global_env: &mut GlobalEnv<'tcx>,
        config: Config,
    ) -> (ParsingUnit, BinaryMetadata<'tcx>) {
        let is_dep = config.dependency;
        let mut this = Self::new(tcx, config);
        this.only_metadata(global_env);
        if is_dep {
            (
                ParsingUnit {
                    prog: Prog::default(),
                    init_data: serde_json::Value::Null,
                },
                global_env.metadata(),
            )
        } else {
            let prog = this.final_prog(global_env);
            (prog, global_env.metadata())
        }
    }
}
