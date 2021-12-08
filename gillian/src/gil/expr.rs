use super::print_utils::comma_separated_display;
use super::{BinOp, Literal, NOp, UnOp};
use std::fmt;

#[derive(Debug, Clone)]
pub enum Expr {
    Lit(Literal),
    PVar(String),
    LVar(String),
    ALoc(String),
    UnOp {
        operator: UnOp,
        operand: Box<Expr>,
    },
    BinOp {
        operator: BinOp,
        left_operand: Box<Expr>,
        right_operand: Box<Expr>,
    },
    NOp {
        operator: NOp,
        operands: Vec<Expr>,
    },
    LstSub {
        list: Box<Expr>,
        start: Box<Expr>,
        end: Box<Expr>,
    },
    EList(Vec<Expr>),
    ESet(Vec<Expr>),
}

impl std::ops::Not for Expr {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Expr::Lit(Literal::Bool(b)) => Expr::Lit(Literal::Bool(!b)),
            _ => Self::UnOp {
                operator: UnOp::UNot,
                operand: Box::new(self),
            },
        }
    }
}

impl From<&str> for Expr {
    fn from(str: &str) -> Self {
        Self::Lit(str.into())
    }
}

impl From<String> for Expr {
    fn from(str: String) -> Self {
        Self::Lit(str.into())
    }
}

impl From<Literal> for Expr {
    fn from(lit: Literal) -> Self {
        Self::Lit(lit)
    }
}

impl From<Vec<Expr>> for Expr {
    fn from(lst: Vec<Expr>) -> Self {
        Self::EList(lst)
    }
}

impl Expr {
    pub fn string(str: String) -> Self {
        Self::Lit(Literal::String(str))
    }

    pub fn bool(b: bool) -> Self {
        Self::Lit(Literal::Bool(b))
    }

    pub fn float(f: f32) -> Self {
        Self::Lit(Literal::Num(f))
    }

    pub fn int(i: i64) -> Self {
        Self::Lit(Literal::Int(i))
    }

    pub fn i_gt(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::bool(i > j),
            _ => !Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::ILessThanEqual,
            },
        }
    }

    pub fn f_gt(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Num(i)), Expr::Lit(Literal::Num(j))) => Expr::bool(i > j),
            _ => !Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::FLessThanEqual,
            },
        }
    }

    pub fn i_lt(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::bool(i < j),
            _ => !Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::ILessThan,
            },
        }
    }

    pub fn f_lt(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Num(i)), Expr::Lit(Literal::Num(j))) => Expr::bool(i < j),
            _ => !Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::FLessThan,
            },
        }
    }

    pub fn lnth(e: Expr, i: usize) -> Self {
        let f: f32 = i as f32;
        match e {
            Expr::EList(vec) => vec.get(i).expect("lnth of a small vector!").to_owned(),
            Expr::Lit(Literal::LList(vec)) => {
                Expr::Lit(vec.get(i).expect("lnth of a small vector!").to_owned())
            }
            _ => Self::BinOp {
                operator: BinOp::LstNth,
                left_operand: Box::new(e),
                right_operand: Box::new(Self::float(f)),
            },
        }
    }

    pub fn lnth_e(e: Expr, i: Expr) -> Self {
        match i {
            Expr::Lit(Literal::Int(i)) => Self::lnth(e, i as usize),
            Expr::Lit(Literal::Num(f)) => Self::lnth(e, f as usize),
            _ => Self::BinOp {
                operator: BinOp::LstNth,
                left_operand: Box::new(e),
                right_operand: Box::new(i),
            },
        }
    }

    pub fn lst_len(e: Expr) -> Self {
        match e {
            Expr::EList(vec) => Expr::int(vec.len() as i64),
            Expr::Lit(Literal::LList(vec)) => Expr::int(vec.len() as i64),
            _ => Expr::UnOp {
                operator: UnOp::LstLen,
                operand: Box::new(e),
            },
        }
    }

    pub fn eq_expr(e1: Expr, e2: Expr) -> Self {
        Expr::BinOp {
            operator: BinOp::Equal,
            left_operand: Box::new(e1),
            right_operand: Box::new(e2),
        }
    }

    pub fn lst_concat(e1: Expr, e2: Expr) -> Self {
        match (e1, e2) {
            (Expr::EList(mut vec1), Expr::EList(mut vec2)) => {
                vec1.append(&mut vec2);
                Expr::EList(vec1)
            }
            (Expr::Lit(Literal::LList(mut vec1)), Expr::Lit(Literal::LList(mut vec2))) => {
                vec1.append(&mut vec2);
                Expr::Lit(Literal::LList(vec1))
            }
            (Expr::EList(vec), x) | (x, Expr::EList(vec)) if vec.is_empty() => x,
            (x, Expr::Lit(Literal::LList(vec))) | (Expr::Lit(Literal::LList(vec)), x)
                if vec.is_empty() =>
            {
                x
            }
            (e1, e2) => Self::NOp {
                operator: NOp::LstCat,
                operands: vec![e1, e2],
            },
        }
    }

    pub fn undefined() -> Self {
        Self::Lit(Literal::Undefined)
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use super::BinOp as BinOpEnum;
        use Expr::*;
        match self {
            Lit(lit) => write!(f, "{}", lit),
            PVar(var) | LVar(var) | ALoc(var) => f.write_str(var),
            UnOp { operator, operand } => write!(f, "({} {})", operator, *operand),
            BinOp {
                operator,
                left_operand,
                right_operand,
            } => match operator {
                BinOpEnum::LstNth | BinOpEnum::StrNth => {
                    write!(f, "{}({}, {})", operator, *left_operand, *right_operand)
                }
                _ => write!(f, "({} {} {})", left_operand, operator, right_operand),
            },
            NOp { operator, operands } => {
                write!(f, "{} (", operator)?;
                comma_separated_display(operands, f)?;
                write!(f, ")")
            }
            LstSub { list, start, end } => {
                write!(f, "l-sub({}, {}, {})", *list, *start, *end)
            }
            EList(vec) => {
                f.write_str("{{ ")?;
                comma_separated_display(vec, f)?;
                f.write_str(" }}")
            }
            ESet(vec) => {
                f.write_str("-{ ")?;
                comma_separated_display(vec, f)?;
                f.write_str(" }-")
            }
        }
    }
}
