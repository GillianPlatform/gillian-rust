use std::fmt;

#[derive(Debug)]
pub enum NOp {
    LstCat,
    SetUnion,
    SetInter,
}

impl fmt::Display for NOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use NOp::*;
        match self {
            LstCat => write!(f, "l+"),
            SetUnion => write!(f, "-u-"),
            SetInter => write!(f, "-i-"),
        }
    }
}
