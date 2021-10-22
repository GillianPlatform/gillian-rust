use super::codeloc::Location;

#[derive(Debug, Default)]
pub struct Annot {
    pub origin_loc: Location,
    pub loop_info: Vec<String>,
}
