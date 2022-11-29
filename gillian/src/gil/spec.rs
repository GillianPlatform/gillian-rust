use super::Assertion;
use std::fmt;

#[derive(Debug)]
pub enum Flag {
    Normal,
    Error,
}

impl fmt::Display for Flag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Flag::Normal => write!(f, "normal"),
            Flag::Error => write!(f, "error"),
        }
    }
}

#[derive(Debug)]
pub struct SingleSpec {
    pub pre: Assertion,
    pub posts: Vec<Assertion>,
    pub flag: Flag,
    pub to_verify: bool,
}

impl fmt::Display for SingleSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "[[ {} ]]", self.pre)?;
        write!(f, "[[")?;
        super::print_utils::separated_display(&self.posts, ";\n", f)?;
        writeln!(f, "]]")?;
        write!(f, "{}", self.flag)
    }
}

#[derive(Debug)]
pub struct Spec {
    pub name: String,
    pub params: Vec<String>,
    pub sspecs: Vec<SingleSpec>,
    pub to_verify: bool,
}

impl fmt::Display for Spec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "spec ")?;
        super::print_utils::write_maybe_quoted(&self.name, f)?;
        write!(f, "(")?;
        super::print_utils::separated_display(&self.params, ",", f)?;
        writeln!(f, ")")?;
        super::print_utils::separated_display(&self.sspecs, ";\n", f)
    }
}
