use std::fmt;

#[derive(Debug, Copy, Clone)]
pub enum Type {
    UndefinedType,
    NullType,
    EmptyType,
    NoneType,
    BoolType,
    IntType,
    NumberType,
    StringType,
    ObjectType,
    ListType,
    TypeType,
    SetType,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Type::*;
        match self {
            UndefinedType => write!(f, "Undefined"),
            NullType => write!(f, "Null"),
            EmptyType => write!(f, "Empty"),
            NoneType => write!(f, "None"),
            BoolType => write!(f, "Bool"),
            IntType => write!(f, "Int"),
            NumberType => write!(f, "Num"),
            StringType => write!(f, "Str"),
            ObjectType => write!(f, "Obj"),
            ListType => write!(f, "List"),
            TypeType => write!(f, "Type"),
            SetType => write!(f, "Set"),
        }
    }
}
