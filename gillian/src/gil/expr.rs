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

impl Expr {
    pub fn string(str: String) -> Self {
        Self::Lit(Literal::String(str))
    }

    pub fn float(f: f32) -> Self {
        Self::Lit(Literal::Num(f))
    }

    pub fn int(i: i64) -> Self {
        Self::Lit(Literal::Int(i))
    }

    pub fn lnth(e: Expr, i: u32) -> Self {
        let f: f32 = i as f32;
        Self::BinOp {
            operator: BinOp::LstNth,
            left_operand: Box::new(e),
            right_operand: Box::new(Self::float(f)),
        }
    }

    pub fn not(e: Expr) -> Self {
        Self::UnOp {
            operator: UnOp::UNot,
            operand: Box::new(e),
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
