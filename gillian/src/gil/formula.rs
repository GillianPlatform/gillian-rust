use std::fmt::Display;

use super::{Expr, Type};

#[derive(Debug)]
pub enum Formula {
    True,
    False,
    Not(Box<Formula>),
    And {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    Or {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    Eq {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    ILess {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    ILessEq {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    FLess {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    FLessEq {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    StrLess {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    SetMem {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    SetSub {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    ForAll {
        quantified: Vec<(String, Option<Type>)>,
        formula: Box<Formula>,
    },
}

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Formula::*;
        match self {
            True => write!(f, "True"),
            False => write!(f, "False"),
            Not(fml) => write!(f, "(! {})", fml),
            And { left, right } => write!(f, "({} /\\ {})", left, right),
            Or { left, right } => write!(f, "({} \\/ {})", left, right),
            Eq { left, right } => write!(f, "({} == {})", left, right),
            ILess { left, right } => write!(f, "({} i<# {})", left, right),
            ILessEq { left, right } => write!(f, "({} i<=# {})", left, right),
            FLess { left, right } => write!(f, "({} <# {})", left, right),
            FLessEq { left, right } => write!(f, "({} <=# {})", left, right),
            StrLess { left, right } => write!(f, "({} s<# {})", left, right),
            SetMem { left, right } => write!(f, "({} --e-- {})", left, right),
            SetSub { left, right } => write!(f, "({} --s-- {})", left, right),
            ForAll {
                quantified,
                formula,
            } => {
                write!(f, "(forall ")?;
                let mut first = true;
                for (name, typ) in quantified {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", name)?;
                    if let Some(typ) = typ {
                        write!(f, ": {}", typ)?;
                    }
                }
                write!(f, ". {})", formula)
            }
        }
    }
}
