use super::{Assertion, Expr};

#[derive(Debug)]
pub struct Lemma {
    pub name: String,
    pub params: Vec<String>,
    pub hyp: Assertion,
    pub concs: Vec<Assertion>,
    pub variant: Option<Expr>,
    pub existentials: Vec<String>,
}