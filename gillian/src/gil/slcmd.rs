use std::fmt::Display;

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
        let display_binders = |f: &mut std::fmt::Formatter<'_>, b: &[String]| {
            if b.is_empty() {
                return Ok(());
            }
            write!(f, "[bind: ")?;
            super::print_utils::separated_display(b, ",", f)?;
            write!(f, "]")
        };
        use SLCmd::*;
        match self {
            ApplyLem {
                lemma_name,
                parameters,
                existentials,
            } => {
                write!(f, "apply ")?;
                super::print_utils::write_maybe_quoted(lemma_name, f)?;
                write!(f, "(")?;
                super::print_utils::separated_display(parameters, ",", f)?;
                write!(f, ")")?;
                display_binders(f, existentials)
            }
            Unfold {
                pred_name,
                parameters,
                bindings,
                rec,
            } => {
                write!(f, "unfold")?;
                if *rec {
                    write!(f, "*")?;
                }
                write!(f, " \"{}\"(", pred_name)?;
                super::print_utils::separated_display(parameters, ", ", f)?;
                write!(f, ")")?;
                if bindings.is_some() {
                    panic!("Can't write unfold with bindings for now: {:#?}", self);
                }
                Ok(())
            }
            Fold {
                pred_name,
                parameters,
                bindings,
            } => {
                write!(f, "fold")?;
                write!(f, " \"{}\"(", pred_name)?;
                super::print_utils::separated_display(parameters, ", ", f)?;
                write!(f, ")")?;
                if bindings.is_some() {
                    panic!("Can't write fold with bindings for now: {:#?}", self);
                }
                Ok(())
            }
            SepAssert {
                assertion,
                existentials,
            } => {
                write!(f, "sep_assert ({})", assertion)?;
                display_binders(f, existentials)
            }
            _ => panic!("Can't write slcmd yet: {:#?}", self),
        }
    }
}
