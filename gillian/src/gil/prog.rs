use std::collections::HashMap;
use super::{Lemma, Proc, Macro, BiSpec, Pred, Spec};

#[derive(Debug)]
pub struct Import {
    pub path: String,
    pub verify: bool,
}

#[derive(Default, Debug)]
pub struct Prog {
    pub imports: Vec<Import>,
    pub lemmas: HashMap<String, Lemma>,
    pub preds: HashMap<String, Pred>,
    pub only_specs: HashMap<String, Spec>,
    pub procs: HashMap<String, Proc>,
    pub macros: HashMap<String, Macro>,
    pub bi_specs: HashMap<String, BiSpec>,
    pub proc_names: Vec<String>,
}