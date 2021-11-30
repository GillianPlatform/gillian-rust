use super::print_utils::comma_separated_display;
use super::{Expr, LCmd, LogicBindings};
use std::fmt;

#[derive(Debug)]
pub struct SinglePhiAssignment {
    pub variable: String,
    pub values: Vec<Expr>,
}

#[derive(Debug)]
pub enum Cmd {
    Skip,
    Assignment {
        variable: String,
        assigned_expr: Expr,
    },
    Action {
        variable: String,
        action_name: String,
        parameters: Vec<Expr>,
    },
    Logic(LCmd),
    Goto(String),
    GuardedGoto {
        guard: Expr,
        then_branch: String,
        else_branch: String,
    },
    Call {
        variable: String,
        proc_ident: Expr,
        parameters: Vec<Expr>,
        error_lab: Option<String>,
        bindings: Option<LogicBindings>,
    },
    ECall {
        variable: String,
        proc_ident: Expr,
        parameters: Vec<Expr>,
        error_lab: Option<String>,
    },
    Apply {
        variable: String,
        args: Expr,
        error_lab: Option<String>,
    },
    PhiAssignment(Vec<SinglePhiAssignment>),
    ReturnNormal,
    ReturnError,
    Fail {
        name: String,
        parameters: Vec<Expr>,
    },
}

impl fmt::Display for Cmd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Cmd::*;
        match self {
            Skip => write!(f, "skip"),
            Assignment {
                variable,
                assigned_expr,
            } => write!(f, "{} := {}", variable, assigned_expr),
            Action {
                variable,
                action_name,
                parameters,
            } => {
                write!(f, "{} := [{}](", variable, action_name)?;
                comma_separated_display(parameters, f)?;
                f.write_str(")")
            }
            Call {
                variable,
                proc_ident,
                parameters,
                error_lab,
                bindings,
            } => {
                assert!(bindings.is_none(), "Cannot print bindings yet");
                write!(f, "{} := {}(", variable, proc_ident)?;
                comma_separated_display(parameters, f)?;
                f.write_str(")")?;
                if let Some(s) = error_lab {
                    write!(f, " with {}", s)?;
                }
                Ok(())
            }
            Goto(str) => write!(f, "goto {}", str),
            ReturnNormal => write!(f, "return"),
            GuardedGoto {
                guard,
                then_branch,
                else_branch,
            } => write!(f, "goto [{}] {} {}", guard, then_branch, else_branch),
            Fail { name, parameters } => {
                write!(f, "fail [{}](", name)?;
                comma_separated_display(parameters, f)?;
                f.write_str(")")
            }
            _ => panic!("Cannot write following command yet: {:#?}", self),
        }
    }
}
