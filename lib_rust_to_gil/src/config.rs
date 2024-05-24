use std::{collections::HashMap, fmt, str::FromStr};

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
    pub in_test: bool,
    pub overrides: HashMap<String, String>,
}

impl Config {
    pub fn of_env() -> Self {
        let in_test = std::env::var("IN_UI_TEST").is_ok();

        let mode = std::env::var("GILLIAN_EXEC_MODE").unwrap_or("verif".into());
        let mode = ExecMode::from_str(&mode).expect(
            "Unspecified execution mode. Please add `GILLIAN_EXEC_MODE=[verif|concrete|symb]`",
        );
        let prophecies = std::env::var("GILLIAN_PROPHECIES").is_ok();

        Config {
            mode,
            prophecies,
            in_test,
            overrides: HashMap::new(),
        }
    }
}
