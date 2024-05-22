use std::fmt;

use pretty::{DocAllocator, Pretty};

#[derive(Debug, Clone, Copy)]
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

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for Constant
where
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        use Constant::*;
        match self {
            Min_float => allocator.text("$$min_value"),
            Max_float => allocator.text("$$max_value"),
            MaxSafeInteger => allocator.text("$$max_safe_integer"),
            Epsilon => allocator.text("$$epsilon"),
            Random => allocator.text("$$random"),
            Pi => allocator.text("$$pi"),
            UTCTime => allocator.text("$$utctime"),
            LocalTime => allocator.text("$$localtime"),
        }
    }
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
