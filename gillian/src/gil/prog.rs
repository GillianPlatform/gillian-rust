use indexmap::IndexMap;

use super::print_utils::separated_display;
use super::{BiSpec, Lemma, Macro, Pred, Proc, Spec};
use std::fmt::{self, Display};

#[derive(Debug, Clone)]
pub struct Import {
    pub path: String,
    pub verify: bool,
}

#[derive(Default, Debug)]
pub struct Prog {
    pub imports: Vec<Import>,
    pub lemmas: IndexMap<String, Lemma>,
    pub preds: IndexMap<String, Pred>,
    pub only_specs: IndexMap<String, Spec>,
    pub procs: IndexMap<String, Proc>,
    pub macros: IndexMap<String, Macro>,
    pub bi_specs: IndexMap<String, BiSpec>,
    pub proc_names: Vec<String>,
}

impl Prog {
    pub fn new(imports: Vec<Import>) -> Self {
        Prog {
            imports,
            ..Default::default()
        }
    }

    pub fn partition_imports(&self) -> (Vec<String>, Vec<String>) {
        let mut regs = vec![];
        let mut vers = vec![];
        for Import { verify, path } in &self.imports {
            if *verify {
                vers.push(format!("\"{}\"", &path));
            } else {
                regs.push(format!("\"{}\"", &path));
            }
        }
        (regs, vers)
    }

    pub fn add_proc(&mut self, proc: Proc) {
        self.proc_names.push(proc.name.clone());
        self.procs.insert(proc.name.clone(), proc);
    }

    pub fn add_pred(&mut self, pred: Pred) {
        self.preds.insert(pred.name.clone(), pred);
    }

    pub fn add_lemma(&mut self, lemma: Lemma) {
        self.lemmas.insert(lemma.name.clone(), lemma);
    }

    pub fn add_only_spec(&mut self, spec: Spec) {
        self.only_specs.insert(spec.name.clone(), spec);
    }
}

impl Display for Prog {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (reg_imports, ver_imports) = self.partition_imports();
        f.write_str("import ")?;
        separated_display(&reg_imports, ", ", f)?;
        assert!(ver_imports.is_empty(), "So far, imports cannot work");
        // f.write_str(";\nimport verify ")?;
        f.write_str(";\n\n")?;
        for spec in self.only_specs.values() {
            f.write_str("axiomatic ")?;
            spec.fmt(f)?;
            f.write_str("\n\n")?;
        }
        for pred in self.preds.values() {
            pred.fmt(f)?;
            f.write_str("\n\n")?;
        }
        for lemma in self.lemmas.values() {
            lemma.fmt(f)?;
            f.write_str("\n\n")?;
        }
        for proc in self.procs.values() {
            proc.fmt(f)?;
            f.write_str("\n\n")?;
        }
        Ok(())
    }
}
