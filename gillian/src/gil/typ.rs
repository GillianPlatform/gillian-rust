use std::fmt;

use pretty::{DocAllocator, Pretty};

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

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for Type
where
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        match self {
            Type::UndefinedType => allocator.text("Undefined"),
            Type::NullType => allocator.text("Null"),
            Type::EmptyType => allocator.text("Empty"),
            Type::NoneType => allocator.text("None"),
            Type::BoolType => allocator.text("Bool"),
            Type::IntType => allocator.text("Int"),
            Type::NumberType => allocator.text("Num"),
            Type::StringType => allocator.text("Str"),
            Type::ObjectType => allocator.text("Obj"),
            Type::ListType => allocator.text("List"),
            Type::TypeType => allocator.text("Type"),
            Type::SetType => allocator.text("Set"),
        }
    }
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
