use std::collections::HashMap;
use std::fmt::Display;

use super::{Expr, Type};

#[derive(Debug, Clone)]
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
        left: Box<Expr>,
        right: Box<Expr>,
    },
    ILessEq {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    FLess {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    FLessEq {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    StrLess {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    SetMem {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    SetSub {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    ForAll {
        quantified: Vec<(String, Option<Type>)>,
        formula: Box<Formula>,
    },
}

impl Formula {
    pub fn subst_pvar(&mut self, mapping: &HashMap<String, String>) {
        match self {
            Self::Not(f) => f.subst_pvar(mapping),
            Self::And { left, right } | Self::Or { left, right } => {
                left.subst_pvar(mapping);
                right.subst_pvar(mapping);
            }
            Self::Eq { left, right }
            | Self::ILess { left, right }
            | Self::ILessEq { left, right }
            | Self::FLess { left, right }
            | Self::FLessEq { left, right }
            | Self::StrLess { left, right }
            | Self::SetMem { left, right }
            | Self::SetSub { left, right } => {
                left.subst_pvar(mapping);
                right.subst_pvar(mapping);
            }
            Self::ForAll { formula, .. } => formula.subst_pvar(mapping),
            _ => (),
        }
    }

    pub fn eq(left: Expr, right: Expr) -> Self {
        Self::Eq {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
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
