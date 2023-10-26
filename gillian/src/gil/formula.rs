use std::fmt::Display;

use super::{Assertion, Expr, Type};

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
    pub fn eq(left: Expr, right: Expr) -> Self {
        Self::Eq {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn and(self, right: Self) -> Self {
        Self::And {
            left: Box::new(self),
            right: Box::new(right),
        }
    }

    pub fn into_asrt(self) -> Assertion {
        self.into()
    }

    pub fn into_expr(self) -> Expr {
        match self {
            Self::True => Expr::bool(true),
            Self::False => Expr::bool(false),
            Self::Not(b) => {
                let b = (*b).into_expr();
                !b
            }
            Self::And { left, right } => {
                let left = (*left).into_expr();
                let right = (*right).into_expr();
                Expr::and(left, right)
            }
            Self::Or { left, right } => {
                let left = (*left).into_expr();
                let right = (*right).into_expr();
                Expr::or(left, right)
            }
            Self::Eq { left, right } => Expr::eq_expr(*left, *right),
            Self::ILess { left, right } => Expr::i_lt(*left, *right),
            Self::ILessEq { left, right } => Expr::i_leq(*left, *right),
            Self::FLess { left, right } => Expr::f_lt(*left, *right),
            Self::FLessEq { left, right } => Expr::f_leq(*left, *right),
            Self::StrLess { .. } => panic!("String less not handled yet"),
            Self::SetMem { .. } => panic!("Set membership less not handled yet"),
            Self::SetSub { .. } => panic!("Set subset not handled yet"),
            Self::ForAll { .. } => panic!("ForAll not handled yet"),
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
