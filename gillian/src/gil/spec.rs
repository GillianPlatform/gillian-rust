use super::Assertion;
use std::fmt;

#[derive(Debug)]
pub enum Flag {
    Normal,
    Error,
}

#[derive(Debug)]
pub struct SingleSpec {
    pub pre: Assertion,
    pub posts: Vec<Assertion>,
    pub flag: Flag,
    pub to_verify: bool,
}

#[derive(Debug)]
pub struct Spec {
    pub name: String,
    pub params: Vec<String>,
    pub sspecs: Vec<SingleSpec>,
    pub to_verify: bool,
}

impl fmt::Display for Flag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Flag::Normal => write!(f, "normal"),
            Flag::Error => write!(f, "error"),
        }
    }
}
