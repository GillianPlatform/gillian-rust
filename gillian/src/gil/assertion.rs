use super::{print_utils::separated_display, visitors::GilVisitorMut};
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
