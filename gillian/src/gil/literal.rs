use super::print_utils::comma_separated_display;
use super::{Constant, Type};
use num_bigint::BigInt;
use std::fmt;

#[derive(Debug, Clone)]
pub enum Literal {
    Undefined,
    Null,
    Empty,
    Constant(Constant),
    Bool(bool),
    Int(BigInt),
    Num(f32),
    String(String),
    Loc(String),
    Type(Type),
    LList(Vec<Literal>),
    Nono,
}

impl Literal {
    pub fn int<I>(i: I) -> Self
    where
        I: Into<BigInt>,
    {
        Self::Int(i.into())
    }
}

macro_rules! from_int {
    ($t: ty) => {
        impl From<$t> for Literal {
            fn from(i: $t) -> Self {
                Self::int(i)
            }
        }
    };

    ($ta: ty, $($tb: ty),+) => {
        from_int!($ta);
        from_int!($($tb),+);
    }
}

from_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl From<&str> for Literal {
    fn from(str: &str) -> Self {
        Self::String(str.to_string())
    }
}

impl From<bool> for Literal {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<Vec<Literal>> for Literal {
    fn from(vec: Vec<Literal>) -> Self {
        Self::LList(vec)
    }
}

impl From<String> for Literal {
    fn from(str: String) -> Self {
        Self::String(str)
    }
}

impl From<f32> for Literal {
    fn from(f: f32) -> Self {
        Self::Num(f)
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Literal::*;
        match self {
            Undefined => write!(f, "undefined"),
            Null => write!(f, "null"),
            Empty => write!(f, "empty"),
            Nono => write!(f, "none"),
            Constant(ct) => write!(f, "{}", ct),
            Bool(b) => {
                if *b {
                    write!(f, "true")
                } else {
                    write!(f, "false")
                }
            }
            Int(i64) => write!(f, "{}i", i64),
            Num(f32) => write!(f, "{}", f32),
            String(str) => write!(f, "\"{}\"", str),
            Loc(loc) => write!(f, "{}", loc),
            Type(typ) => write!(f, "{}", typ),
            LList(vec) => {
                f.write_str("{{ ")?;
                comma_separated_display(vec, f)?;
                f.write_str(" }}")
            }
        }
    }
}
