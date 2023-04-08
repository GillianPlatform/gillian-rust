use super::print_utils::separated_display;
use super::{BinOp, Literal, NOp, UnOp};
use num_bigint::BigInt;
use std::collections::HashMap;
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

macro_rules! from_lit {
    ($t: ty) => {
        impl From<$t> for Expr {
            fn from(x: $t) -> Self {
                let y: Literal = x.into();
                Expr::Lit(y)
            }
        }
    };

    ($ta: ty, $($tb: ty),+) => {
        from_lit!($ta);

        from_lit!($($tb),+);
    };
}

from_lit!(
    Literal, &str, String, bool, f32, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128,
    isize
);

macro_rules! from_array {
    ($l:literal) => {
        impl<T: Into<Expr>> From<[T; $l]> for Expr {
            fn from(x: [T; $l]) -> Self {
                let vec = x.into_iter().map(|v| v.into()).collect();
                Expr::EList(vec)
            }
        }
    };

    ($l:literal, $($ls:literal),+) => {
        from_array!($l);
        from_array!($($ls),+);
    };
}

from_array!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);

impl From<Vec<Expr>> for Expr {
    fn from(lst: Vec<Expr>) -> Self {
        Self::EList(lst)
    }
}

impl Expr {
    pub fn string(str: String) -> Self {
        str.into()
    }

    pub fn bool(b: bool) -> Self {
        b.into()
    }

    pub fn float(f: f32) -> Self {
        f.into()
    }

    pub fn int<T>(i: T) -> Self
    where
        T: Into<BigInt>,
    {
        Expr::Lit(Literal::Int(i.into()))
    }

    pub fn null() -> Self {
        Literal::Null.into()
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
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::ILessThan,
            },
        }
    }

    pub fn f_lt(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Num(i)), Expr::Lit(Literal::Num(j))) => Expr::bool(i < j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::FLessThan,
            },
        }
    }

    pub fn lnth<I>(self, i: I) -> Self
    where
        I: Into<BigInt> + Clone,
    {
        let bg: BigInt = i.clone().into();
        let us: Result<usize, _> = bg.try_into();
        match (&self, us) {
            (Expr::EList(vec), Ok(idx)) => vec.get(idx).expect("lnth of small vector!").to_owned(),
            (Expr::Lit(Literal::LList(vec)), Ok(idx)) => {
                Expr::Lit(vec.get(idx).expect("lnth of a small vector!").to_owned())
            }
            _ => Self::BinOp {
                operator: BinOp::LstNth,
                left_operand: Box::new(self),
                right_operand: Box::new(Self::int(i)),
            },
        }
    }

    pub fn lnth_e(e: Expr, i: Expr) -> Self {
        match i {
            Expr::Lit(Literal::Int(i)) => Self::lnth(e, i),
            Expr::Lit(Literal::Num(f)) => Self::lnth(e, f as usize),
            _ => Self::BinOp {
                operator: BinOp::LstNth,
                left_operand: Box::new(e),
                right_operand: Box::new(i),
            },
        }
    }

    pub fn lst_len(self) -> Self {
        match self {
            Expr::EList(vec) => Expr::int(vec.len()),
            Expr::Lit(Literal::LList(vec)) => Expr::int(vec.len()),
            _ => Expr::UnOp {
                operator: UnOp::LstLen,
                operand: Box::new(self),
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

    pub fn eq_f<E: Into<Expr>>(self, e2: E) -> super::Formula {
        super::Formula::eq(self, e2.into())
    }

    pub fn lst_concat(self, e2: Expr) -> Self {
        match (self, e2) {
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

    pub fn plus(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::int(i + j),
            _ => Expr::BinOp {
                operator: BinOp::IPlus,
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
            },
        }
    }
    pub fn minus(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::int(i - j),
            _ => Expr::BinOp {
                operator: BinOp::IMinus,
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
            },
        }
    }

    pub fn undefined() -> Self {
        Self::Lit(Literal::Undefined)
    }

    pub fn subst_pvar(&mut self, mapping: &HashMap<String, Expr>) {
        match self {
            Self::PVar(s) => {
                if let Some(e) = mapping.get(s) {
                    *self = e.clone();
                }
            }
            Self::BinOp {
                left_operand,
                right_operand,
                ..
            } => {
                left_operand.subst_pvar(mapping);
                right_operand.subst_pvar(mapping);
            }
            Self::UnOp { operand, .. } => {
                operand.subst_pvar(mapping);
            }
            Self::EList(vec) | Expr::ESet(vec) | Expr::NOp { operands: vec, .. } => {
                for e in vec {
                    e.subst_pvar(mapping);
                }
            }
            Self::LstSub { list, start, end } => {
                list.subst_pvar(mapping);
                start.subst_pvar(mapping);
                end.subst_pvar(mapping);
            }
            Self::ALoc(..) | Self::LVar(..) | Self::Lit(..) => {}
        }
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
                separated_display(operands, ", ", f)?;
                write!(f, ")")
            }
            LstSub { list, start, end } => {
                write!(f, "l-sub({}, {}, {})", *list, *start, *end)
            }
            EList(vec) => {
                f.write_str("{{ ")?;
                separated_display(vec, ", ", f)?;
                f.write_str(" }}")
            }
            ESet(vec) => {
                f.write_str("-{ ")?;
                separated_display(vec, ", ", f)?;
                f.write_str(" }-")
            }
        }
    }
}
