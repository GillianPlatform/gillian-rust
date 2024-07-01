/// Fresh lvar name generator
#[derive(Debug)]
pub struct TempGenerator {
    cur_lvar: u32,
}

impl TempGenerator {
    pub fn new() -> Self {
        Self { cur_lvar: 0 }
    }

    pub fn fresh_lvar(&mut self) -> String {
        let temp = format!("#lvar_{}", self.cur_lvar);
        self.cur_lvar += 1;
        temp
    }
}
