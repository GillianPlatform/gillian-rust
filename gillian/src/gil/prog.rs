use super::{BiSpec, Lemma, Macro, Pred, Proc, Spec};
use std::collections::HashMap;
use std::fmt::{self, Display};

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

impl Prog {
    pub fn add_proc(&mut self, proc: Proc) {
        self.proc_names.push(proc.name.clone());
        self.procs.insert(proc.name.clone(), proc);
    }
}

impl Display for Prog {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (_, proc) in &self.procs {
            proc.fmt(f)?;
            f.write_str("\n\n")?;
        }
        Ok(())
    }
}
