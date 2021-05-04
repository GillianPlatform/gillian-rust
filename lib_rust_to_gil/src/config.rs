use std::fmt;

pub enum ExecMode {
    Concrete,
    Symbolic,
    Verification,
    Act,
}

impl fmt::Debug for ExecMode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExecMode::Concrete => write!(f, "concrete"),
            ExecMode::Symbolic => write!(f, "symbolic"),
            ExecMode::Verification => write!(f, "verification"),
            ExecMode::Act => write!(f, "act"),
        }
    }
}

#[derive(Debug)]
pub struct Config {
    pub mode: ExecMode,
}
