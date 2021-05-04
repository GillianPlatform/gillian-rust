pub enum ExecMode {
    Concrete,
    Symbolic,
    Verification,
    Act,
}

pub struct Config {
    pub mode: ExecMode,
}
