use std::fmt::Display;

use super::{Expr, Formula, SLCmd, Type};

#[derive(Debug)]
pub enum LCmd {
    If {
        guard: Expr,
        then_branch: Box<LCmd>,
        else_branch: Box<LCmd>,
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

impl Display for LCmd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use LCmd::*;
        match self {
            If {
                guard,
                then_branch,
                else_branch,
            } => write!(
                f,
                "if ({}) then {{ {} }} else {{ {} }}",
                guard, then_branch, else_branch
            ),
            Branch(formula) => write!(f, "branch ({})", formula),
            Assert(formula) => write!(f, "assert ({})", formula),
            Assume(formula) => write!(f, "assume ({})", formula),
            AssumeType { variable, typ } => write!(f, "assume_type ({}, {})", variable, typ),
            FreshSVar(variable) => write!(f, "{} := fresh_svar()", variable),
            SL(sl_cmd) => sl_cmd.fmt(f),
        }
    }
}
