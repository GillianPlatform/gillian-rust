use std::fmt::Display;

use pretty::{docs, DocAllocator, Pretty};

use super::{Assertion, Expr, LCmd};

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

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for &'a Lemma
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        let name = super::print_utils::maybe_quoted(&self.name);
        docs![
            alloc,
            "lemma ",
            name,
            alloc
                .intersperse(
                    self.params.iter().map(|expr| expr.pretty(alloc)),
                    alloc.text(", "),
                )
                .parens(),
            self.hyp.pretty(alloc).enclose("\n[[\n", "\n]]"),
            alloc
                .intersperse(self.concs.iter(), ";\n")
                .enclose("\n[[", "\n]]"),
            if let Some(proof) = &self.proof {
                alloc
                    .intersperse(proof.iter(), ";\n")
                    .nest(2)
                    .enclose("\n[*", "\n*]")
            } else {
                alloc.nil()
            }
        ]
    }
}

impl Display for Lemma {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alloc = pretty::Arena::new();
        self.pretty(&alloc).render_fmt(80, f)
    }
}
