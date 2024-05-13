use super::print_utils::separated_display;
use super::visitors::GilVisitorMut;
use super::{BinOp, Literal, NOp, UnOp};
use num_bigint::BigInt;
use num_traits::cast::ToPrimitive;
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
        length: Box<Expr>,
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
    pub fn lvar<S>(s: S) -> Self
    where
        S: Into<String>,
    {
        Expr::LVar(s.into())
    }

    pub fn pvar<S>(s: S) -> Self
    where
        S: Into<String>,
    {
        Expr::PVar(s.into())
    }

    pub fn string<S>(s: S) -> Self
    where
        S: ToString,
    {
        s.to_string().into()
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

    pub fn implies(self, other: Self) -> Self {
        self.e_not().e_or(other)
    }

    pub fn e_or(self, other: Self) -> Self {
        match (self, other) {
            (Expr::Lit(Literal::Bool(bl)), Expr::Lit(Literal::Bool(br))) => {
                Expr::Lit(Literal::Bool(bl || br))
            }
            (Expr::Lit(Literal::Bool(true)), _) | (_, Expr::Lit(Literal::Bool(true))) => {
                Expr::Lit(Literal::Bool(true))
            }
            (Expr::Lit(Literal::Bool(false)), e) | (e, Expr::Lit(Literal::Bool(false))) => e,
            (e1, e2) => Self::BinOp {
                operator: BinOp::BOr,
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
            },
        }
    }

    pub fn e_not(self) -> Self {
        match self {
            Expr::Lit(Literal::Bool(b)) => Expr::Lit(Literal::Bool(!b)),
            Expr::UnOp {
                operator: UnOp::UNot,
                operand: b,
            } => *b,
            _ => Self::UnOp {
                operator: UnOp::UNot,
                operand: Box::new(self),
            },
        }
    }

    pub fn null() -> Self {
        Literal::Null.into()
    }

    pub fn i_mul(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::int(i * j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::ITimes,
            },
        }
    }

    pub fn f_mul(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Num(i)), Expr::Lit(Literal::Num(j))) => Expr::float(i * j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::FTimes,
            },
        }
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

    pub fn i_le(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::bool(i <= j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::ILessThanEqual,
            },
        }
    }

    pub fn f_le(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Num(i)), Expr::Lit(Literal::Num(j))) => Expr::bool(i <= j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::FLessThanEqual,
            },
        }
    }

    pub fn i_shl(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => {
                Expr::int(i << j.to_u128().unwrap())
            }
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::LeftShift,
            },
        }
    }

    pub fn i_leq(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::bool(i <= j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::ILessThanEqual,
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

    pub fn f_leq(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Num(i)), Expr::Lit(Literal::Num(j))) => Expr::bool(i <= j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::FLessThanEqual,
            },
        }
    }

    pub fn lnth_e(self, e: Expr) -> Self {
        match e {
            Expr::Lit(Literal::Int(i)) => self.lnth(i),
            e => Self::BinOp {
                operator: BinOp::LstNth,
                left_operand: Box::new(self),
                right_operand: Box::new(e),
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

    pub fn repeat(self, amount: Expr) -> Self {
        match amount {
            Expr::Lit(Literal::Int(i)) => {
                let values = std::iter::repeat(self)
                    .take(i.to_usize().unwrap())
                    .collect();
                Expr::EList(values)
            }
            amount => Self::BinOp {
                operator: BinOp::LstRepeat,
                left_operand: Box::new(self),
                right_operand: Box::new(amount),
            },
        }
    }

    pub fn lst_sub_e(self, start: Expr, length: Expr) -> Self {
        match (start, length) {
            (Expr::Lit(Literal::Int(start)), Expr::Lit(Literal::Int(length))) => {
                self.lst_sub(start, length)
            }
            (start, length) => Self::LstSub {
                list: Box::new(self),
                start: Box::new(start),
                length: Box::new(length),
            },
        }
    }

    pub fn lst_sub<I, J>(self, start: I, length: J) -> Self
    where
        I: Into<BigInt> + Clone,
        J: Into<BigInt> + Clone,
    {
        let start: BigInt = start.clone().into();
        let length: BigInt = length.clone().into();
        let start_us: Result<usize, _> = start.clone().try_into();
        let length_us: Result<usize, _> = length.clone().try_into();
        match (self, start_us, length_us) {
            (Expr::EList(vec), Ok(start), Ok(length)) => {
                let result = vec.into_iter().skip(start).take(length).collect::<Vec<_>>();
                if result.len() != length {
                    panic!("ListSub is invalid!");
                }
                Expr::EList(result)
            }
            (Expr::Lit(Literal::LList(vec)), Ok(start), Ok(length)) => {
                let result: Vec<_> = vec
                    .into_iter()
                    .skip(start)
                    .take(length)
                    .map(Expr::from)
                    .collect();
                if result.len() != length {
                    panic!("ListSub is invalid!");
                }
                Expr::EList(result)
            }
            (x, _, _) => Self::LstSub {
                list: Box::new(x),
                start: Box::new(Expr::int(start)),
                length: Box::new(Expr::int(length)),
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

    pub fn lst_head(self) -> Self {
        match self {
            Expr::EList(vec) => {
                if vec.is_empty() {
                    panic!("lst_head on empty list");
                }
                vec[0].clone()
            }
            s => Self::UnOp {
                operator: UnOp::Car,
                operand: Box::new(s),
            },
        }
    }

    pub fn lst_tail(self) -> Self {
        match self {
            Expr::EList(mut vec) => {
                if vec.is_empty() {
                    panic!("lst_head on empty list");
                }
                vec.remove(0);
                Expr::EList(vec)
            }
            s => Self::UnOp {
                operator: UnOp::Cdr,
                operand: Box::new(s),
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

    pub fn and(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Bool(i)), Expr::Lit(Literal::Bool(j))) => Expr::bool(*i && *j),
            _ => Expr::BinOp {
                operator: BinOp::BAnd,
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
            },
        }
    }

    pub fn or(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Bool(i)), Expr::Lit(Literal::Bool(j))) => Expr::bool(*i || *j),
            _ => Expr::BinOp {
                operator: BinOp::BOr,
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
            },
        }
    }

    pub fn undefined() -> Self {
        Self::Lit(Literal::Undefined)
    }

    pub fn subst_pvar(&mut self, mapping: &HashMap<String, Expr>) {
        let mut visitor = super::visitors::SubstPVar::new(mapping);
        visitor.visit_expr(self);
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
                BinOpEnum::LstNth | BinOpEnum::StrNth | BinOpEnum::LstRepeat => {
                    write!(f, "{}({}, {})", operator, *left_operand, *right_operand)
                }
                _ => write!(f, "({} {} {})", left_operand, operator, right_operand),
            },
            NOp { operator, operands } => {
                write!(f, "{} (", operator)?;
                separated_display(operands, ", ", f)?;
                write!(f, ")")
            }
            LstSub {
                list,
                start,
                length: end,
            } => {
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
