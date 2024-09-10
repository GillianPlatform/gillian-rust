use indexmap::IndexMap;
use pretty::{docs, DocAllocator, Pretty};

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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alloc = pretty::Arena::new();
        self.pretty(&alloc).render_fmt(80, f)
    }
}

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for &'a Prog
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        let mut doc = alloc.nil();
        let (reg_imports, ver_imports) = self.partition_imports();

        let imports = docs![
            alloc,
            "import ",
            alloc.intersperse(reg_imports, ", "),
            ";",
            alloc.line(),
            alloc.line()
        ];

        doc = doc.append(imports);

        assert!(ver_imports.is_empty(), "So far, imports cannot work");

        for spec in self.only_specs.values() {
            let sdoc = docs![
                alloc,
                "axiomatic ",
                format!("{spec}"),
                alloc.line(),
                alloc.line()
            ];

            doc = doc.append(sdoc);
        }

        for pred in self.preds.values() {
            let sdoc = docs![alloc, pred, alloc.line(), alloc.line()];

            doc = doc.append(sdoc);
        }
        for lemma in self.lemmas.values() {
            let sdoc = docs![alloc, format!("{lemma}"), alloc.line(), alloc.line()];

            doc = doc.append(sdoc);
        }
        for proc in self.procs.values() {
            let sdoc = docs![alloc, format!("{proc}"), alloc.line(), alloc.line()];

            doc = doc.append(sdoc);
        }
        doc
    }
}
