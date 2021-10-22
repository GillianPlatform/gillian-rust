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
    Less {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    LessEq {
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
