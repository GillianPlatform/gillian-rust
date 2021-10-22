use super::LCmd;

#[derive(Debug)]
pub struct Macro {
    pub name: String,
    pub params: Vec<String>,
    pub definition: Vec<LCmd>,
}