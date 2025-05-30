use pretty::{docs, DocAllocator, Pretty};

use super::{
    print_utils::separated_display,
    visitors::{GilVisitorMut, PVartoLVar},
};
use std::{collections::HashMap, fmt::Display};

use super::{Expr, Formula, Type};

#[derive(Debug, Clone)]
pub enum Assertion {
    Emp,
    Star {
        left: Box<Assertion>,
        right: Box<Assertion>,
    },
    Pred {
        name: String,
        params: Vec<Expr>,
    },
    Pure(Formula),
    Types(Vec<(Expr, Type)>),
    GA {
        name: String,
        ins: Vec<Expr>,
        outs: Vec<Expr>,
    },
    Wand {
        lhs: (String, Vec<Expr>),
        rhs: (String, Vec<Expr>),
    },
}

impl Assertion {
    pub fn wand(lhs: (String, Vec<Expr>), rhs: (String, Vec<Expr>)) -> Self {
        Self::Wand { lhs, rhs }
    }

    pub fn pred_call_of_tuple((name, params): (String, Vec<Expr>)) -> Self {
        Self::Pred { name, params }
    }

    pub fn star(self, right: Self) -> Self {
        match (self, right) {
            (Assertion::Emp, x) | (x, Assertion::Emp) => x,
            (x, y) => Assertion::Star {
                left: Box::new(x),
                right: Box::new(y),
            },
        }
    }

    pub fn unstar(self) -> Vec<Self> {
        let mut comps = Vec::new();
        self.unstar_inner(&mut comps);
        comps
    }

    fn unstar_inner(self, comps: &mut Vec<Self>) {
        match self {
            Self::Star { left, right } => {
                left.unstar_inner(comps);
                right.unstar_inner(comps);
            }
            _ => comps.push(self),
        }
    }

    pub fn subst_pvar(&mut self, subst: &HashMap<String, Expr>) {
        let mut visitor = super::visitors::SubstPVar::new(subst);
        visitor.visit_assertion(self);
    }

    pub fn subst_lvar(&mut self, subst: &HashMap<String, Expr>) {
        let mut visitor = super::visitors::SubstLVar::new(subst);
        visitor.visit_assertion(self);
    }

    pub fn pvar_to_lvar(mut self) -> Self {
        PVartoLVar.visit_assertion(&mut self);
        self
    }
}

impl FromIterator<Assertion> for Assertion {
    fn from_iter<I: IntoIterator<Item = Assertion>>(iter: I) -> Self {
        iter.into_iter().fold(Assertion::Emp, Self::star)
    }
}

impl From<Formula> for Assertion {
    fn from(value: Formula) -> Self {
        Assertion::Pure(value)
    }
}

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for &'a Assertion
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        match self {
            Assertion::Emp => alloc.text("emp"),
            Assertion::Star { left, right } => {
                docs![alloc, &**left, alloc.line(), "* ", &**right].group()
            }
            Assertion::Pred { name, params } => {
                let name = super::print_utils::maybe_quoted(name);

                alloc.text(name.clone()).append(
                    alloc
                        .intersperse(
                            params.iter().map(|expr| expr.pretty(alloc)),
                            alloc.text(", "),
                        )
                        .parens(),
                )
            }
            Assertion::Pure(formula) => formula.pretty(alloc),
            Assertion::Types(types) => alloc.text("types").append(
                alloc
                    .intersperse(
                        types.iter().map(|(expr, ty)| {
                            expr.pretty(alloc).append(": ").append(ty.pretty(alloc))
                        }),
                        alloc.text(", "),
                    )
                    .parens(),
            ),
            Assertion::GA { name, ins, outs } => alloc
                .text(super::print_utils::maybe_quoted(name))
                .enclose("<", ">")
                .append(
                    alloc
                        .intersperse(ins.iter().map(|expr| expr.pretty(alloc)), alloc.text(", "))
                        .append("; ")
                        .append(alloc.intersperse(
                            outs.iter().map(|expr| expr.pretty(alloc)),
                            alloc.text(", "),
                        ))
                        .parens(),
                ),
            Assertion::Wand { lhs, rhs } => alloc
                .text(super::print_utils::maybe_quoted(&lhs.0))
                .append(
                    alloc
                        .intersperse(
                            lhs.1.iter().map(|expr| expr.pretty(alloc)),
                            alloc.text(", "),
                        )
                        .parens(),
                )
                .append(alloc.line())
                .append("-* ")
                .append(
                    alloc.text(super::print_utils::maybe_quoted(&rhs.0)).append(
                        alloc
                            .intersperse(
                                rhs.1.iter().map(|expr| expr.pretty(alloc)),
                                alloc.text(", "),
                            )
                            .parens()
                            .nest(2),
                    ),
                )
                .group()
                .nest(2)
                .parens(),
        }
    }
}

impl Display for Assertion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Assertion::*;
        match self {
            Emp => write!(f, "emp"),
            Star { left, right } => write!(f, "{} * {}", left, right),
            Pred { name, params } => {
                super::print_utils::write_maybe_quoted(name, f)?;
                write!(f, "(")?;
                separated_display(params, ", ", f)?;
                write!(f, ")")
            }
            Pure(formula) => formula.fmt(f),
            Types(types) => {
                write!(f, "types(")?;
                let mut first = true;
                for (expr, ty) in types {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", expr, ty)?;
                }
                write!(f, ")")
            }
            GA { name, ins, outs } => {
                write!(f, "<{}>(", name)?;
                separated_display(ins, ", ", f)?;
                write!(f, "; ")?;
                separated_display(outs, ", ", f)?;
                write!(f, ")")
            }
            Wand {
                lhs: (lname, lhs_args),
                rhs: (rname, rhs_args),
            } => {
                write!(f, "(")?;
                super::print_utils::write_maybe_quoted(lname, f)?;
                write!(f, "(")?;
                separated_display(lhs_args, ", ", f)?;
                write!(f, ") -* ")?;
                super::print_utils::write_maybe_quoted(rname, f)?;
                write!(f, "(")?;
                separated_display(rhs_args, ", ", f)?;
                write!(f, "))")
            }
        }
    }
}
