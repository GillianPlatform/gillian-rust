use std::fmt;

#[derive(Debug, Clone)]
pub enum Constant {
    Min_float,
    Max_float,
    MaxSafeInteger,
    Epsilon,
    Random,
    Pi,
    UTCTime,
    LocalTime,
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Constant::*;
        match self {
            Min_float => write!(f, "$$min_value"),
            Max_float => write!(f, "$$max_value"),
            MaxSafeInteger => write!(f, "$$max_safe_integer"),
            Epsilon => write!(f, "$$epsilon"),
            Random => write!(f, "$$random"),
            Pi => write!(f, "$$pi"),
            UTCTime => write!(f, "$$utctime"),
            LocalTime => write!(f, "$$localtime"),
        }
    }
}
