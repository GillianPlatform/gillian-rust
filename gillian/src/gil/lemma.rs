use std::fmt::Display;

use pretty::{docs, DocAllocator, Pretty};

use super::{print_utils, Assertion, Expr, LCmd};

#[derive(Debug)]
pub struct Lemma {
    pub name: String,
    pub params: Vec<String>,
    pub hyp: Assertion,
    pub concs: Vec<Assertion>,
    pub proof: Option<Vec<LCmd>>,
    pub variant: Option<Expr>,
    pub existentials: Vec<String>,
}

impl Display for Lemma {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alloc = pretty::Arena::new();
        self.pretty(&alloc).render_fmt(80, f)
    }
}

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for &'a Lemma
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        let header = alloc
            .text("lemma ")
            .append(print_utils::maybe_quoted(&self.name))
            .append(alloc.text("("))
            .append(alloc.intersperse(self.params.iter().map(|p| alloc.text(p)), alloc.text(", ")))
            .append(alloc.text(")"))
            .group();

        let hyps = docs![alloc, alloc.line(), self.hyp.pretty(alloc), alloc.line()]
            .group()
            .nest(2)
            .enclose("[[", "]]")
            .append(alloc.hardline());
        let concs = docs![
            alloc,
            alloc.line(),
            alloc.intersperse(&self.concs, ";\n"),
            alloc.line()
        ]
        .group()
        .nest(2)
        .enclose("[[", "]]");

        let proof = match &self.proof {
            Some(p) => alloc
                .intersperse(p, ";\n")
                .group()
                .nest(2)
                .enclose("[* ", " *]"),
            None => alloc.nil(),
        };

        header.append(hyps).append(concs).append(proof)
    }
}
