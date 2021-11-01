use super::print_utils::comma_separated_display;
use super::{Constant, Type};
use std::fmt;

#[derive(Debug, Clone)]
pub enum Literal {
    Undefined,
    Null,
    Empty,
    Constant(Constant),
    Bool(bool),
    Int(i64),
    Num(f32),
    String(String),
    Loc(String),
    Type(Type),
    LList(Vec<Literal>),
    Nono,
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
                f.write_str("(")?;
                comma_separated_display(vec, f)?;
                f.write_str(")")
            }
        }
    }
}
