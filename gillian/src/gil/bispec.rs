use super::Assertion;

#[derive(Debug)]
pub struct BiSpec {
    pub name: String,
    pub params: Vec<String>,
    pub pres: Vec<Assertion>,
}
