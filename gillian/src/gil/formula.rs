use std::fmt::Display;

use pretty::{DocAllocator, Pretty};

use super::{Assertion, Expr, Literal, Type};

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
    Impl {
        left: Box<Formula>,
        right: Box<Formula>,
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

impl From<bool> for Formula {
    fn from(value: bool) -> Self {
        if value {
            Self::True
        } else {
            Self::False
        }
    }
}

impl Formula {
    pub fn i_le<E1, E2>(e1: E1, e2: E2) -> Self
    where
        E1: Into<Expr>,
        E2: Into<Expr>,
    {
        let e1 = e1.into();
        let e2 = e2.into();
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => (i <= j).into(),
            _ => Self::ILessEq {
                left: Box::new(e1),
                right: Box::new(e2),
            },
        }
    }

    pub fn eq(left: Expr, right: Expr) -> Self {
        Self::Eq {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn forall(quant: (String, Option<Type>), mut formula: Self) -> Self {
        if let Formula::ForAll { quantified, .. } = &mut formula {
            quantified.push(quant);
            formula
        } else {
            Formula::ForAll {
                quantified: vec![quant],
                formula: Box::new(formula),
            }
        }
    }

    pub fn fnot(self) -> Self {
        match self {
            Formula::True => Formula::False,
            Formula::False => Formula::True,
            _ => Formula::Not(Box::new(self)),
        }
    }

    pub fn implies(self, right: Self) -> Self {
        match (&self, &right) {
            (Formula::True, _) => right,
            (Formula::False, _) | (_, Formula::True) => Formula::True,
            (_, Formula::False) => self.fnot(),
            _ => Self::Impl {
                left: Box::new(self),
                right: Box::new(right),
            },
        }
    }

    pub fn or(self, right: Self) -> Self {
        match (&self, &right) {
            (Formula::False, _) => right,
            (_, Formula::False) => self,
            (Formula::True, _) | (_, Formula::True) => Formula::True,
            _ => Self::Or {
                left: Box::new(self),
                right: Box::new(right),
            },
        }
    }

    pub fn and(self, right: Self) -> Self {
        match (&self, &right) {
            (Formula::True, _) => right,
            (_, Formula::True) => self,
            (Formula::False, _) | (_, Formula::False) => Formula::False,
            _ => Self::And {
                left: Box::new(self),
                right: Box::new(right),
            },
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
            Self::Impl { left, right } => {
                let left = (*left).into_expr();
                let right = (*right).into_expr();
                Expr::implies(left, right)
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

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for &'a Formula
where
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        use Formula::*;
        match self {
            True => allocator.text("True"),
            False => allocator.text("False"),
            Not(fml) => allocator
                .text("(! ")
                .append(fml.pretty(allocator))
                .append(")"),
            And { left, right } => left
                .pretty(allocator)
                .append(" /\\ ")
                .append(right.pretty(allocator))
                .parens(),
            Or { left, right } => left
                .pretty(allocator)
                .append(" \\/ ")
                .append(right.pretty(allocator))
                .parens(),
            Eq { left, right } => left
                .pretty(allocator)
                .append(" == ")
                .append(right.pretty(allocator))
                .parens(),
            Impl { left, right } => left
                .pretty(allocator)
                .append(" ==> ")
                .append(right.pretty(allocator))
                .parens(),
            ILess { left, right } => left
                .pretty(allocator)
                .append(" i<# ")
                .append(right.pretty(allocator))
                .parens(),
            ILessEq { left, right } => left
                .pretty(allocator)
                .append(" i<=# ")
                .append(right.pretty(allocator))
                .parens(),
            FLess { left, right } => left
                .pretty(allocator)
                .append(" <# ")
                .append(right.pretty(allocator))
                .parens(),
            FLessEq { left, right } => left
                .pretty(allocator)
                .append(" <=# ")
                .append(right.pretty(allocator))
                .parens(),
            StrLess { left, right } => left
                .pretty(allocator)
                .append(" s<# ")
                .append(right.pretty(allocator))
                .parens(),
            SetMem { left, right } => left
                .pretty(allocator)
                .append(" --e-- ")
                .append(right.pretty(allocator))
                .parens(),
            SetSub { left, right } => left
                .pretty(allocator)
                .append(" --s-- ")
                .append(right.pretty(allocator))
                .parens(),
            ForAll {
                quantified,
                formula,
            } => allocator
                .text("forall ")
                .append(allocator.intersperse(
                    quantified.iter().map(|(name, ty)| {
                        if let Some(ty) = ty {
                            allocator.text(format!("{}: {}", name, ty))
                        } else {
                            allocator.text(name)
                        }
                    }),
                    ", ",
                ))
                .append(". ")
                .append(formula.pretty(allocator))
                .parens(),
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
            Impl { left, right } => write!(f, "({} ==> {})", left, right),
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
