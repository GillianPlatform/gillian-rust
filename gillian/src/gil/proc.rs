use super::print_utils::comma_separated_display;
use super::{Annot, Cmd, Spec};
use std::fmt::{self, Write};

#[derive(Debug)]
pub struct ProcBodyItem {
    pub annot: Annot,
    pub label: Option<String>,
    pub cmd: Cmd,
}

#[derive(Debug, Default)]
pub struct Proc {
    pub name: String,
    pub body: Vec<ProcBodyItem>,
    pub params: Vec<String>,
    pub spec: Option<Spec>,
}

impl From<Cmd> for ProcBodyItem {
    fn from(cmd: Cmd) -> Self {
        ProcBodyItem {
            cmd,
            annot: Annot::default(),
            label: None,
        }
    }
}

impl Proc {
    pub fn new(name: String, params: Vec<String>, body: Vec<ProcBodyItem>) -> Self {
        Proc {
            name,
            params,
            body,
            ..Proc::default()
        }
    }

    pub fn longest_label(&self) -> usize {
        let mut max = 0;
        for ProcBodyItem { label, .. } in &self.body {
            match label {
                None => (),
                Some(lab) => {
                    max = std::cmp::max(max, lab.len());
                }
            };
        }
        max
    }
}

impl fmt::Display for Proc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let longest_label = self.longest_label();
        let indent = "  ";
        let empty_string = String::new();
        write!(f, "proc {}(", self.name)?;
        comma_separated_display(&self.params, f)?;
        write!(f, ") {{\n")?;
        for ProcBodyItem { label, cmd, .. } in &self.body {
            let semi = label.is_some();
            let label = label.as_ref();
            let label: &String = label.unwrap_or(&empty_string);
            f.write_str(indent)?;
            write!(f, "{}", label)?;
            if semi {
                f.write_char(':')?;
            } else {
                f.write_char(' ')?;
            }
            for _ in 0..(longest_label - label.len() + 1) {
                f.write_str(" ")?;
            }
            write!(f, "{};\n", cmd)?;
        }
        f.write_str("}")
    }
}

pub mod proc_body {
    use super::*;
    pub fn set_first_label(items: &mut Vec<ProcBodyItem>, label: String) {
        assert!(!items.is_empty(), "Empty block!");
        let item = items.get_mut(0).unwrap();
        item.label = Some(label);
    }
    
    pub fn body_from_commands(items: Vec<Cmd>) -> Vec<ProcBodyItem> {
        items.into_iter().map(|x| ProcBodyItem::from(x)).collect()
    }
    
}
