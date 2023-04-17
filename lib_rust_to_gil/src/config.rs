use std::{fmt, str::FromStr};

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum ExecMode {
    Concrete,
    Symbolic,
    Verification,
    Act,
}

impl FromStr for ExecMode {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "verif" | "verification" | "v" => Ok(Self::Verification),
            "concrete" | "c" | "conc" => Ok(Self::Concrete),
            "act" | "bi" => Ok(Self::Act),
            "wpst" | "symb" | "s" => Ok(Self::Symbolic),
            _ => Err(format!("Invalid execution mode: {}!", s)),
        }
    }
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

#[derive(Debug, Clone)]
pub struct Config {
    pub mode: ExecMode,
    pub prophecies: bool,
}

impl Config {
    pub fn of_args(args: &mut Vec<String>) -> Self {
        let mode = args
            .iter()
            .find_map(|x| x.strip_prefix("--gillian-exec-mode="))
            .map(|x| ExecMode::from_str(x).unwrap())
            .expect(
                "Unspecified execution mode. Please add `--gillian-exec-mode=[verif|concrete|symb]",
            );
        let prophecies = args.iter().any(|x| x == "--gillian-prophecies");
        args.retain(|a| (a != "--gillian-prophecies") && !a.starts_with("--gillian-exec-mode="));
        Config { mode, prophecies }
    }
}
