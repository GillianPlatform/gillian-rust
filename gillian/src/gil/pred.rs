use std::fmt::Display;

use super::{print_utils, Assertion, Formula, Type};

#[derive(Debug, Clone)]
pub struct Pred {
    pub name: String,
    pub num_params: usize,
    pub params: Vec<(String, Option<Type>)>,
    pub ins: Vec<usize>,
    pub definitions: Vec<Assertion>,
    pub pure: bool,
    pub abstract_: bool,
    pub facts: Vec<Formula>,
    pub guard: Option<Assertion>,
}

impl Display for Pred {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.abstract_ {
            write!(f, "abstract ")?;
        }
        if self.pure {
            write!(f, "pure ")?;
        }

        write!(f, "pred ")?;
        print_utils::write_maybe_quoted(&self.name, f)?;
        write!(f, "(")?;
        for (i, (name, typ)) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            if self.ins.contains(&i) {
                write!(f, "+")?;
            }
            write!(f, "{}", &name)?;
            if let Some(typ) = typ {
                write!(f, ": {}", typ)?;
            }
        }
        write!(f, ")")?;
        if !self.definitions.is_empty() {
            writeln!(f, ":")?;
            super::print_utils::separated_display(&self.definitions, ", ", f)?;
        }
        writeln!(f, ";")?;
        if !self.facts.is_empty() {
            write!(f, "facts: ")?;
            let mut first = false;
            for fact in &self.facts {
                if first {
                    first = false;
                } else {
                    writeln!(f, " and ")?;
                }
                write!(f, "{}", fact)?;
            }
        }
        if let Some(guard) = &self.guard {
            writeln!(f, "guard: {};", guard)?;
        }
        Ok(())
    }
}
