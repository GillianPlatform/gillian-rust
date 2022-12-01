use super::print_utils::{separated_display, write_maybe_quoted};
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
        if let Some(spec) = &self.spec {
            writeln!(f, "{}\n", spec)?;
        }

        let longest_label = self.longest_label();
        let indent = "  ";
        let empty_string = String::new();
        write!(f, "proc ")?;
        write_maybe_quoted(&self.name, f)?;
        write!(f, "(")?;
        separated_display(&self.params, ", ", f)?;
        writeln!(f, ") {{")?;
        let mut is_first = true;
        for ProcBodyItem { label, cmd, .. } in &self.body {
            if is_first {
                is_first = false;
            } else {
                f.write_str(";\n")?;
            }
            let colon = label.is_some();
            let label = label.as_ref();
            let label: &String = label.unwrap_or(&empty_string);
            f.write_str(indent)?;
            write!(f, "{}", label)?;
            if colon {
                f.write_char(':')?;
            } else {
                f.write_char(' ')?;
            }
            for _ in 0..(longest_label - label.len() + 1) {
                f.write_str(" ")?;
            }
            write!(f, "{}", cmd)?;
        }
        f.write_str("\n};")
    }
}

#[derive(Debug)]
pub struct ProcBody(Vec<ProcBodyItem>);

impl From<ProcBody> for Vec<ProcBodyItem> {
    fn from(body: ProcBody) -> Self {
        body.0
    }
}

impl From<Vec<ProcBodyItem>> for ProcBody {
    fn from(items: Vec<ProcBodyItem>) -> Self {
        ProcBody(items)
    }
}

impl From<Vec<Cmd>> for ProcBody {
    fn from(cmds: Vec<Cmd>) -> Self {
        cmds.into_iter()
            .map(ProcBodyItem::from)
            .collect::<Vec<_>>()
            .into()
    }
}

impl Default for ProcBody {
    fn default() -> Self {
        // Estimate of an ok capacity
        Self::from(Vec::<ProcBodyItem>::with_capacity(20))
    }
}

impl ProcBody {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn append(&mut self, mut other: Self) {
        self.0.append(&mut other.0)
    }

    pub fn push_cmd(&mut self, cmd: Cmd, label: Option<String>) {
        self.0.push(ProcBodyItem {
            annot: Annot::default(),
            label,
            cmd,
        })
    }

    pub fn set_first_label(&mut self, label: String) {
        assert!(!self.0.is_empty(), "Cannot add label to empty block!");
        let item = self.0.get_mut(0).unwrap();
        item.label = Some(label);
    }
}
