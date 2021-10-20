use super::gil::*;
use std::fmt::{self, Write};

fn comma_separated_display(
    vec: &Vec<impl fmt::Display>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    let mut sep = "";
    for elem in vec {
        f.write_str(sep)?;
        write!(f, "{}", elem)?;
        sep = ", ";
    }
    Ok(())
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

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BinOp::*;
        match self {
            Equal => write!(f, "="),
            ILessThan => write!(f, "i<"),
            ILessThanEqual => write!(f, "i<="),
            IPlus => write!(f, "i+"),
            IMinus => write!(f, "i-"),
            ITimes => write!(f, "i*"),
            IDiv => write!(f, "i/"),
            IMod => write!(f, "i%"),
            FLessThan => write!(f, "<"),
            FLessThanEqual => write!(f, "<="),
            FPlus => write!(f, "+"),
            FMinus => write!(f, "-"),
            FTimes => write!(f, "*"),
            FDiv => write!(f, "/"),
            FMod => write!(f, "%"),
            SLessThan => write!(f, "s<"),
            BAnd => write!(f, "and"),
            BOr => write!(f, "or"),
            BitwiseAnd => write!(f, "&"),
            BitwiseOr => write!(f, "|"),
            BitwiseXor => write!(f, "^"),
            LeftShift => write!(f, "<<"),
            SignedRightShift => write!(f, ">>"),
            UnsignedRightShift => write!(f, ">>>"),
            BitwiseAndL => write!(f, "&l"),
            BitwiseOrL => write!(f, "|l"),
            BitwiseXorL => write!(f, "^l"),
            LeftShiftL => write!(f, "<<l"),
            SignedRightShiftL => write!(f, ">>l"),
            UnsignedRightShiftL => write!(f, ">>>l"),
            M_atan2 => write!(f, "m_atan2"),
            M_pow => write!(f, "**"),
            LstNth => write!(f, "l-nth"),
            StrCat => write!(f, "++"),
            StrNth => write!(f, "s-nth"),
            SetDiff => write!(f, "-d-"),
            BSetMem => write!(f, "-e-"),
            BSetSub => write!(f, "-s-"),
        }
    }
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use UnOp::*;
        match self {
            IUnaryMinus => write!(f, "i-"),
            FUnaryMinus => write!(f, "-"),
            UNot => write!(f, "not"),
            BitwiseNot => write!(f, "~"),
            M_isNaN => write!(f, "isNaN"),
            M_abs => write!(f, "m_abs"),
            M_acos => write!(f, "m_acos"),
            M_asin => write!(f, "m_asin"),
            M_atan => write!(f, "m_atan"),
            M_ceil => write!(f, "m_ceil"),
            M_cos => write!(f, "m_cos"),
            M_exp => write!(f, "m_exp"),
            M_floor => write!(f, "m_floor"),
            M_log => write!(f, "m_log"),
            M_round => write!(f, "m_round"),
            M_sgn => write!(f, "m_sgn"),
            M_sin => write!(f, "m_sin"),
            M_sqrt => write!(f, "m_sqrt"),
            M_tan => write!(f, "m_tan"),
            ToStringOp => write!(f, "num_to_string"),
            ToIntOp => write!(f, "num_to_int"),
            ToUint16Op => write!(f, "num_to_uint16"),
            ToInt32Op => write!(f, "num_to_int32"),
            ToUint32Op => write!(f, "num_to_uint32"),
            ToNumberOp => write!(f, "string_to_num"),
            TypeOf => write!(f, "typeOf"),
            Car => write!(f, "car"),
            Cdr => write!(f, "cdr"),
            LstLen => write!(f, "l-len"),
            LstRev => write!(f, "l-rev"),
            StrLen => write!(f, "s-len"),
            SetToList => write!(f, "set_to_list"),
        }
    }
}

impl fmt::Display for NOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use NOp::*;
        match self {
            LstCat => write!(f, "l+"),
            SetUnion => write!(f, "-u-"),
            SetInter => write!(f, "-i-"),
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Literal::*;
        match self {
            Undefined => write!(f, "undefined"),
            Null => write!(f, "null"),
            Empty => write!(f, "empty"),
            Nono => write!(f, "none"),
            Constant(ct) => write!(f, "{}", ct),
            Bool(b) => {
                if *b {
                    write!(f, "true")
                } else {
                    write!(f, "false")
                }
            }
            Int(i64) => write!(f, "{}i", i64),
            Num(f32) => write!(f, "{}", f32),
            String(str) => write!(f, "\"{}\"", str),
            Loc(loc) => write!(f, "{}", loc),
            Type(typ) => write!(f, "{}", typ),
            LList(vec) => {
                f.write_str("(")?;
                comma_separated_display(vec, f)?;
                f.write_str(")")
            }
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use super::gil::BinOp as BinOpEnum;
        use Expr::*;
        match self {
            Lit(lit) => write!(f, "{}", lit),
            PVar(var) | LVar(var) | ALoc(var) => f.write_str(var),
            UnOp { operator, operand } => write!(f, "({} {})", operator, *operand),
            BinOp {
                operator,
                left_operand,
                right_operand,
            } => match operator {
                BinOpEnum::LstNth | BinOpEnum::StrNth => {
                    write!(f, "{}({}, {})", operator, *left_operand, *right_operand)
                }
                _ => write!(f, "({} {} {})", left_operand, operator, right_operand),
            },
            NOp { operator, operands } => {
                write!(f, "{} (", operator)?;
                comma_separated_display(operands, f)?;
                write!(f, ")")
            }
            LstSub { list, start, end } => {
                write!(f, "l-sub({}, {}, {})", *list, *start, *end)
            }
            EList(vec) => {
                f.write_str("{{ ")?;
                comma_separated_display(vec, f)?;
                f.write_str(" }}")
            }
            ESet(vec) => {
                f.write_str("-{ ")?;
                comma_separated_display(vec, f)?;
                f.write_str(" }-")
            }
        }
    }
}

impl fmt::Display for Cmd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Cmd::*;
        match self {
            Skip => write!(f, "skip"),
            Assignment {
                variable,
                assigned_expr,
            } => write!(f, "{} := {}", variable, assigned_expr),
            Action {
                variable,
                action_name,
                parameters,
            } => {
                write!(f, "{} := [{}](", variable, action_name)?;
                comma_separated_display(parameters, f)?;
                f.write_str(")")
            }
            Goto(str) => write!(f, "goto {}", str),
            ReturnNormal => write!(f, "return"),
            _ => panic!("Cannot write following command yet: {:#?}", self),
        }
    }
}

impl fmt::Display for Flag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Flag::Normal => write!(f, "normal"),
            Flag::Error => write!(f, "error"),
        }
    }
}

impl fmt::Display for Proc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let longest_label = self.longest_label();
        let indent = "  ";
        let empty_string = String::new();
        write!(f, "proc {}(", self.proc_name)?;
        comma_separated_display(&self.proc_params, f)?;
        write!(f, ") {{\n")?;
        for ProcBodyItem { label, cmd, .. } in &self.proc_body {
            let semi = label.is_some();
            let label = label.as_ref();
            let label: &String = label.unwrap_or(&empty_string);
            f.write_str(indent)?;
            write!(f, "{}", label)?;
            if semi {
                f.write_char(':')?;
            }
            for _ in 0..(longest_label - label.len() + 1) {
                f.write_str(" ")?;
            }
            write!(f, "{};\n", cmd)?;
        }
        f.write_str("}")
    }
}
