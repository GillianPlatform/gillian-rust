use super::{Expr, Formula, SLCmd, Type};

#[derive(Debug)]
pub enum LCmd {
    If {
        guard: Expr,
        then_branch: Box<LCmd>,
        else_branch: Box<LCmd>,
    },
    Branch(Formula),
    Macro {
        macro_name: String,
        parameters: Vec<Expr>,
    },
    Assert(Formula),
    Assume(Formula),
    AssumeType {
        variable: String,
        typ: Type,
    },
    SpecVar(Vec<String>),
    SL(SLCmd),
}
