use super::{Type, Assertion};

#[derive(Debug)]
pub struct DefinitionLabel {
    pub name: String,
    pub existentials: Vec<String>,
}

#[derive(Debug)]
pub struct PredDefinition {
    pub lab_opt: Option<DefinitionLabel>,
    pub assertion: Assertion,
}

#[derive(Debug)]
pub struct Pred {
    pub name: String,
    pub num_params: i32,
    pub params: Vec<(String, Option<Type>)>,
    pub ins: Vec<i32>,
    pub definitions: Vec<PredDefinition>,
    pub pure: bool,
    pub normalised: bool,
}