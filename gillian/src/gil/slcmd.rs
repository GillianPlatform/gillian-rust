use super::{Assertion, Expr};

#[derive(Debug)]
pub struct LogicBindings {
    pub name: String,
    pub binds: Vec<(String, Expr)>,
}

#[derive(Debug)]
pub enum SLCmd {
    Fold {
        pred_name: String,
        parameters: Vec<Expr>,
        bindings: Option<LogicBindings>,
    },
    Unfold {
        pred_name: String,
        parameters: Vec<Expr>,
        bindings: Option<LogicBindings>,
        rec: bool,
    },
    GUnfold(String),
    ApplyLem {
        lemma_name: String,
        parameters: Vec<Expr>,
        existentials: Vec<String>,
    },
    SepAssert {
        assertion: Assertion,
        existentials: Vec<String>,
    },
    Invariant {
        assertion: Assertion,
        existentials: Vec<String>,
    },
}
