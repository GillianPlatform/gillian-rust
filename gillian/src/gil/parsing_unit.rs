use super::Prog;
use std::fmt::{self, Display};

pub struct ParsingUnit {
    pub prog: Prog,
    pub init_data: serde_json::Value,
}

impl Display for ParsingUnit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "#begin_init_data\n{}\n#end_init_data\n\n{}",
            self.init_data, self.prog
        )
    }
}
