use std::fmt::Display;

use super::{Assertion, Expr};

#[derive(Debug)]
pub struct Lemma {
    pub name: String,
    pub params: Vec<String>,
    pub hyp: Assertion,
    pub concs: Vec<Assertion>,
    pub variant: Option<Expr>,
    pub existentials: Vec<String>,
}

impl Display for Lemma {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "lemma {}(", self.name)?;
        super::print_utils::separated_display(&self.params, ", ", f)?;
        write!(f, ")")?;
        writeln!(f, "[[ {} ]]", self.hyp)?;
        write!(f, "[[")?;
        super::print_utils::separated_display(&self.concs, ";\n", f)?;
        writeln!(f, "]]")
    }
}
