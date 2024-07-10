use std::fmt::Display;

use pretty::{docs, DocAllocator, Pretty};

use super::{Expr, Formula, SLCmd, Type};

#[derive(Debug)]
pub enum LCmd {
    If {
        guard: Expr,
        then_branch: Vec<LCmd>,
        else_branch: Vec<LCmd>,
    },
    Branch(Formula),
    Assert(Formula),
    Assume(Formula),
    AssumeType {
        variable: String,
        typ: Type,
    },
    FreshSVar(String),
    SL(SLCmd),
}

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for &'a LCmd
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        match self {
            LCmd::If {
                guard,
                then_branch,
                else_branch,
            } => {
                docs![
                    alloc,
                    "if ",
                    guard.pretty(alloc).parens(),
                    " then ",
                    alloc.intersperse(then_branch, alloc.line()).braces(),
                    " else ",
                    alloc.intersperse(else_branch, alloc.line()).braces(),
                ]
            }
            LCmd::Branch(f) => {
                docs![alloc, "branch ", f.pretty(alloc).parens()]
            }
            LCmd::Assert(f) => docs![alloc, "assert ", f.pretty(alloc).parens()],
            LCmd::Assume(f) => docs![alloc, "assume ", f.pretty(alloc).parens()],
            LCmd::AssumeType { variable, typ } => {
                docs![alloc, "assume_type ", "(", variable, ",", typ.clone(), ")"]
            }
            LCmd::FreshSVar(v) => docs![alloc, v, " := ", "fresh_svar", "()"],
            LCmd::SL(sl) => docs![alloc, format!("{sl}")],
        }
    }
}

impl Display for LCmd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alloc = pretty::Arena::new();
        self.pretty(&alloc).render_fmt(80, f)
    }
}
