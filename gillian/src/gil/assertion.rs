use super::print_utils::comma_separated_display;
use std::fmt::Display;

use super::{Expr, Formula, Type};

#[derive(Debug)]
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
                comma_separated_display(params, f)?;
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
                comma_separated_display(ins, f)?;
                write!(f, "; ")?;
                comma_separated_display(outs, f)?;
                write!(f, ")")
            }
        }
    }
}
