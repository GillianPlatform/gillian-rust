use std::fmt::Display;

use pretty::{docs, DocAllocator, Pretty};

use crate::gil::print_utils;

use super::{Assertion, Expr};

#[derive(Debug)]
pub struct LogicBindings {
    pub name: String,
    pub binds: Vec<(String, Expr)>,
}

#[derive(Debug)]
pub enum SLCmd {
    Fold {
        pred_name: String,
        parameters: Vec<Expr>,
        bindings: Option<LogicBindings>,
    },
    Unfold {
        pred_name: String,
        parameters: Vec<Expr>,
        bindings: Option<LogicBindings>,
        rec: bool,
    },
    Package {
        lhs: (String, Vec<Expr>),
        rhs: (String, Vec<Expr>),
    },
    GUnfold(String),
    ApplyLem {
        lemma_name: String,
        parameters: Vec<Expr>,
        existentials: Vec<String>,
    },
    SepAssert {
        assertion: Assertion,
        existentials: Vec<String>,
    },
    Invariant {
        assertion: Assertion,
        existentials: Vec<String>,
    },
}

impl Display for SLCmd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alloc = pretty::Arena::new();
        self.pretty(&alloc).render_fmt(80, f)
    }
}

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for &'a SLCmd
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D> {
        use SLCmd::*;
        match self {
            ApplyLem {
                lemma_name,
                parameters,
                existentials,
            } => {
                let apply_doc = docs![
                    alloc,
                    "apply ",
                    print_utils::maybe_quoted(lemma_name),
                    alloc.intersperse(parameters, ", ").parens()
                ];

                if !existentials.is_empty() {
                    apply_doc
                        .append(alloc.space())
                        .append(alloc.text("[bind:"))
                        .append(alloc.space())
                        .append(alloc.intersperse(existentials.iter().map(|e| alloc.text(e)), ", "))
                        .append(alloc.text("]"))
                } else {
                    apply_doc
                }
            }
            Unfold {
                pred_name,
                parameters,
                bindings,
                rec,
            } => {
                let mut unfold_doc = alloc.text("unfold");
                if *rec {
                    unfold_doc = unfold_doc.append(alloc.text("*"));
                }
                unfold_doc = unfold_doc
                    .append(alloc.space())
                    .append(print_utils::maybe_quoted(pred_name))
                    .append(alloc.intersperse(parameters, ", ").parens());
                if bindings.is_some() {
                    unfold_doc.append(alloc.text(" // Bindings not implemented"))
                } else {
                    unfold_doc
                }
            }
            Fold {
                pred_name,
                parameters,
                bindings,
            } => {
                let fold_doc = alloc
                    .text("fold")
                    .append(alloc.space())
                    .append(print_utils::maybe_quoted(pred_name))
                    .append(alloc.intersperse(parameters, ", ").parens());

                if bindings.is_some() {
                    fold_doc.append(alloc.text(" // Bindings not implemented"))
                } else {
                    fold_doc
                }
            }
            Package {
                lhs: (lname, largs),
                rhs: (rname, rargs),
            } => alloc
                .text("package")
                .append(alloc.space())
                .append(alloc.text("("))
                .append(alloc.line_())
                .append(print_utils::maybe_quoted(lname))
                .append(alloc.intersperse(largs, ", ").parens())
                .append(alloc.line())
                .append(alloc.text("-*"))
                .append(alloc.line())
                .append(print_utils::maybe_quoted(rname))
                .append(alloc.intersperse(rargs, ", ").parens())
                .append(alloc.text(")")),
            SepAssert {
                assertion,
                existentials,
            } => {
                let assert_doc = alloc
                    .text("sep_assert")
                    .append(alloc.space())
                    .append(assertion.pretty(alloc).parens());

                if !existentials.is_empty() {
                    assert_doc
                        .append(alloc.space())
                        .append(alloc.text("[bind:"))
                        .append(alloc.space())
                        .append(alloc.intersperse(existentials, ", "))
                        .append(alloc.text("]"))
                } else {
                    assert_doc
                }
            }
            GUnfold(pred_name) => alloc
                .text("gunfold")
                .append(alloc.space())
                .append(alloc.text(pred_name)),
            Invariant {
                assertion,
                existentials,
            } => {
                let invariant_doc = alloc
                    .text("invariant")
                    .append(alloc.space())
                    .append(assertion.pretty(alloc).parens());

                if !existentials.is_empty() {
                    invariant_doc
                        .append(alloc.space())
                        .append(alloc.text("[bind:"))
                        .append(alloc.space())
                        .append(alloc.intersperse(existentials, ", "))
                        .append(alloc.text("]"))
                } else {
                    invariant_doc
                }
            }
        }
    }
}
