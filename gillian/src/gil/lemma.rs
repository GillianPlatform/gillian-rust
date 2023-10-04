use std::fmt::Display;

use super::{Assertion, Expr, LCmd};

#[derive(Debug)]
pub struct Lemma {
    pub name: String,
    pub params: Vec<String>,
    pub hyp: Assertion,
    pub concs: Vec<Assertion>,
    pub proof: Option<Vec<LCmd>>,
    pub variant: Option<Expr>,
    pub existentials: Vec<String>,
}

impl Display for Lemma {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "lemma ")?;
        super::print_utils::write_maybe_quoted(&self.name, f)?;
        write!(f, "(")?;
        super::print_utils::separated_display(&self.params, ", ", f)?;
        write!(f, ")")?;
        writeln!(f, "[[ {} ]]", self.hyp)?;
        write!(f, "[[")?;
        super::print_utils::separated_display(&self.concs, ";\n", f)?;
        writeln!(f, "]]")?;
        if let Some(proof) = &self.proof {
            writeln!(f, "\n[*")?;
            super::print_utils::separated_display(proof, ";\n", f)?;
            writeln!(f, "\n*]")?;
        }
        Ok(())
    }
}
