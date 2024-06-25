use super::print_utils::separated_display;
use super::visitors::GilVisitorMut;
use super::{Literal, Type};
use num_bigint::BigInt;
use num_traits::cast::ToPrimitive;
use pretty::{docs, DocAllocator, Pretty};
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone)]
pub enum Expr {
    Lit(Literal),
    PVar(String),
    LVar(String),
    ALoc(String),
    UnOp {
        operator: UnOp,
        operand: Box<Expr>,
    },
    BinOp {
        operator: BinOp,
        left_operand: Box<Expr>,
        right_operand: Box<Expr>,
    },
    NOp {
        operator: NOp,
        operands: Vec<Expr>,
    },
    LstSub {
        list: Box<Expr>,
        start: Box<Expr>,
        length: Box<Expr>,
    },
    EList(Vec<Expr>),
    ESet(Vec<Expr>),
    EExists(Vec<(String, Option<Type>)>, Box<Expr>),
}

impl std::ops::Not for Expr {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Expr::Lit(Literal::Bool(b)) => Expr::Lit(Literal::Bool(!b)),
            _ => Self::UnOp {
                operator: UnOp::UNot,
                operand: Box::new(self),
            },
        }
    }
}

macro_rules! from_lit {
    ($t: ty) => {
        impl From<$t> for Expr {
            fn from(x: $t) -> Self {
                let y: Literal = x.into();
                Expr::Lit(y)
            }
        }
    };

    ($ta: ty, $($tb: ty),+) => {
        from_lit!($ta);

        from_lit!($($tb),+);
    };
}

from_lit!(
    Literal, &str, String, bool, f32, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128,
    isize, BigInt
);

macro_rules! from_array {
    ($l:literal) => {
        impl<T: Into<Expr>> From<[T; $l]> for Expr {
            fn from(x: [T; $l]) -> Self {
                let vec = x.into_iter().map(|v| v.into()).collect();
                Expr::EList(vec)
            }
        }
    };

    ($l:literal, $($ls:literal),+) => {
        from_array!($l);
        from_array!($($ls),+);
    };
}

from_array!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);

impl From<Vec<Expr>> for Expr {
    fn from(lst: Vec<Expr>) -> Self {
        Self::EList(lst)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum NOp {
    LstCat,
    SetUnion,
    SetInter,
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

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for NOp
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        match self {
            NOp::LstCat => alloc.text("l+"),
            NOp::SetUnion => alloc.text("-u-"),
            NOp::SetInter => alloc.text("-i-"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    IUnaryMinus,
    FUnaryMinus,
    UNot,
    BitwiseNot,
    M_isNaN,
    M_abs,
    M_acos,
    M_asin,
    M_atan,
    M_ceil,
    M_cos,
    M_exp,
    M_floor,
    M_log,
    M_round,
    M_sgn,
    M_sin,
    M_sqrt,
    M_tan,
    ToStringOp,
    ToIntOp,
    ToUint16Op,
    ToUint32Op,
    ToInt32Op,
    ToNumberOp,
    TypeOf,
    Car,
    Cdr,
    LstLen,
    LstRev,
    SetToList,
    StrLen,
}

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for UnOp
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        use UnOp::*;
        match self {
            IUnaryMinus => alloc.text("i-"),
            FUnaryMinus => alloc.text("-"),
            UNot => alloc.text("not"),
            BitwiseNot => alloc.text("~"),
            M_isNaN => alloc.text("isNaN"),
            M_abs => alloc.text("m_abs"),
            M_acos => alloc.text("m_acos"),
            M_asin => alloc.text("m_asin"),
            M_atan => alloc.text("m_atan"),
            M_ceil => alloc.text("m_ceil"),
            M_cos => alloc.text("m_cos"),
            M_exp => alloc.text("m_exp"),
            M_floor => alloc.text("m_floor"),
            M_log => alloc.text("m_log"),
            M_round => alloc.text("m_round"),
            M_sgn => alloc.text("m_sgn"),
            M_sin => alloc.text("m_sin"),
            M_sqrt => alloc.text("m_sqrt"),
            M_tan => alloc.text("m_tan"),
            ToStringOp => alloc.text("num_to_string"),
            ToIntOp => alloc.text("num_to_int"),
            ToUint16Op => alloc.text("num_to_uint16"),
            ToInt32Op => alloc.text("num_to_int32"),
            ToUint32Op => alloc.text("num_to_uint32"),
            ToNumberOp => alloc.text("string_to_num"),
            TypeOf => alloc.text("typeOf"),
            Car => alloc.text("car"),
            Cdr => alloc.text("cdr"),
            LstLen => alloc.text("l-len"),
            LstRev => alloc.text("l-rev"),
            SetToList => alloc.text("set_to_list"),
            StrLen => alloc.text("s-len"),
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

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Equal,
    ILessThan,
    ILessThanEqual,
    IPlus,
    IMinus,
    ITimes,
    IDiv,
    IMod,
    FLessThan,
    FLessThanEqual,
    FPlus,
    FMinus,
    FTimes,
    FDiv,
    FMod,
    SLessThan,
    BAnd,
    BOr,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    LeftShift,
    SignedRightShift,
    UnsignedRightShift,
    BitwiseAndL,
    BitwiseOrL,
    BitwiseXorL,
    LeftShiftL,
    SignedRightShiftL,
    UnsignedRightShiftL,
    M_atan2,
    M_pow,
    LstNth,
    LstRepeat,
    StrCat,
    StrNth,
    SetDiff,
    BSetMem,
    BSetSub,
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
            LstRepeat => write!(f, "l-repeat"),
            StrCat => write!(f, "++"),
            StrNth => write!(f, "s-nth"),
            SetDiff => write!(f, "-d-"),
            BSetMem => write!(f, "-e-"),
            BSetSub => write!(f, "-s-"),
        }
    }
}

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for BinOp
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        use BinOp::*;
        match self {
            Equal => alloc.text("="),
            ILessThan => alloc.text("i<"),
            ILessThanEqual => alloc.text("i<="),
            IPlus => alloc.text("i+"),
            IMinus => alloc.text("i-"),
            ITimes => alloc.text("i*"),
            IDiv => alloc.text("i/"),
            IMod => alloc.text("i%"),
            FLessThan => alloc.text("<"),
            FLessThanEqual => alloc.text("<="),
            FPlus => alloc.text("+"),
            FMinus => alloc.text("-"),
            FTimes => alloc.text("*"),
            FDiv => alloc.text("/"),
            FMod => alloc.text("%"),
            SLessThan => alloc.text("s<"),
            BAnd => alloc.text("and"),
            BOr => alloc.text("or"),
            BitwiseAnd => alloc.text("&"),
            BitwiseOr => alloc.text("|"),
            BitwiseXor => alloc.text("^"),
            LeftShift => alloc.text("<<"),
            SignedRightShift => alloc.text(">>"),
            UnsignedRightShift => alloc.text(">>>"),
            BitwiseAndL => alloc.text("&l"),
            BitwiseOrL => alloc.text("|l"),
            BitwiseXorL => alloc.text("^l"),
            LeftShiftL => alloc.text("<<l"),
            SignedRightShiftL => alloc.text(">>l"),
            UnsignedRightShiftL => alloc.text(">>>l"),
            M_atan2 => alloc.text("m_atan2"),
            M_pow => alloc.text("**"),
            LstNth => alloc.text("l-nth"),
            LstRepeat => alloc.text("l-repeat"),
            StrCat => alloc.text("++"),
            StrNth => alloc.text("s-nth"),
            SetDiff => alloc.text("-d-"),
            BSetMem => alloc.text("-e-"),
            BSetSub => alloc.text("-s-"),
        }
    }
}

impl Expr {
    pub fn lvar<S>(s: S) -> Self
    where
        S: Into<String>,
    {
        Expr::LVar(s.into())
    }

    pub fn pvar<S>(s: S) -> Self
    where
        S: Into<String>,
    {
        Expr::PVar(s.into())
    }

    pub fn string<S>(s: S) -> Self
    where
        S: ToString,
    {
        s.to_string().into()
    }

    pub fn bool(b: bool) -> Self {
        b.into()
    }

    pub fn float(f: f32) -> Self {
        f.into()
    }

    pub fn int<T>(i: T) -> Self
    where
        T: Into<BigInt>,
    {
        Expr::Lit(Literal::Int(i.into()))
    }

    pub fn implies(self, other: Self) -> Self {
        self.e_not().e_or(other)
    }

    pub fn e_or(self, other: Self) -> Self {
        match (self, other) {
            (Expr::Lit(Literal::Bool(bl)), Expr::Lit(Literal::Bool(br))) => {
                Expr::Lit(Literal::Bool(bl || br))
            }
            (Expr::Lit(Literal::Bool(true)), _) | (_, Expr::Lit(Literal::Bool(true))) => {
                Expr::Lit(Literal::Bool(true))
            }
            (Expr::Lit(Literal::Bool(false)), e) | (e, Expr::Lit(Literal::Bool(false))) => e,
            (e1, e2) => Self::BinOp {
                operator: BinOp::BOr,
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
            },
        }
    }

    pub fn e_not(self) -> Self {
        match self {
            Expr::Lit(Literal::Bool(b)) => Expr::Lit(Literal::Bool(!b)),
            Expr::UnOp {
                operator: UnOp::UNot,
                operand: b,
            } => *b,
            _ => Self::UnOp {
                operator: UnOp::UNot,
                operand: Box::new(self),
            },
        }
    }

    pub fn null() -> Self {
        Literal::Null.into()
    }

    pub fn i_mul(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::int(i * j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::ITimes,
            },
        }
    }

    pub fn f_mul(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Num(i)), Expr::Lit(Literal::Num(j))) => Expr::float(i * j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::FTimes,
            },
        }
    }

    pub fn i_gt(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::bool(i > j),
            _ => !Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::ILessThanEqual,
            },
        }
    }

    pub fn f_gt(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Num(i)), Expr::Lit(Literal::Num(j))) => Expr::bool(i > j),
            _ => !Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::FLessThanEqual,
            },
        }
    }

    pub fn i_lt(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::bool(i < j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::ILessThan,
            },
        }
    }

    pub fn i_le(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::bool(i <= j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::ILessThanEqual,
            },
        }
    }

    pub fn f_le(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Num(i)), Expr::Lit(Literal::Num(j))) => Expr::bool(i <= j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::FLessThanEqual,
            },
        }
    }

    pub fn i_shl(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => {
                Expr::int(i << j.to_u128().unwrap())
            }
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::LeftShift,
            },
        }
    }

    pub fn i_leq(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::bool(i <= j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::ILessThanEqual,
            },
        }
    }

    pub fn f_lt(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Num(i)), Expr::Lit(Literal::Num(j))) => Expr::bool(i < j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::FLessThan,
            },
        }
    }

    pub fn f_leq(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Num(i)), Expr::Lit(Literal::Num(j))) => Expr::bool(i <= j),
            _ => Expr::BinOp {
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
                operator: BinOp::FLessThanEqual,
            },
        }
    }

    pub fn lnth_e(self, e: Expr) -> Self {
        match e {
            Expr::Lit(Literal::Int(i)) => self.lnth(i),
            e => Self::BinOp {
                operator: BinOp::LstNth,
                left_operand: Box::new(self),
                right_operand: Box::new(e),
            },
        }
    }

    pub fn lnth<I>(self, i: I) -> Self
    where
        I: Into<BigInt> + Clone,
    {
        let bg: BigInt = i.clone().into();
        let us: Result<usize, _> = bg.try_into();
        match (&self, us) {
            (Expr::EList(vec), Ok(idx)) => vec.get(idx).expect("lnth of small vector!").to_owned(),
            (Expr::Lit(Literal::LList(vec)), Ok(idx)) => {
                Expr::Lit(vec.get(idx).expect("lnth of a small vector!").to_owned())
            }
            _ => Self::BinOp {
                operator: BinOp::LstNth,
                left_operand: Box::new(self),
                right_operand: Box::new(Self::int(i)),
            },
        }
    }

    pub fn repeat(self, amount: Expr) -> Self {
        match amount {
            Expr::Lit(Literal::Int(i)) => {
                let values = std::iter::repeat(self)
                    .take(i.to_usize().unwrap())
                    .collect();
                Expr::EList(values)
            }
            amount => Self::BinOp {
                operator: BinOp::LstRepeat,
                left_operand: Box::new(self),
                right_operand: Box::new(amount),
            },
        }
    }

    pub fn lst_sub_e(self, start: Expr, length: Expr) -> Self {
        match (start, length) {
            (Expr::Lit(Literal::Int(start)), Expr::Lit(Literal::Int(length))) => {
                self.lst_sub(start, length)
            }
            (start, length) => Self::LstSub {
                list: Box::new(self),
                start: Box::new(start),
                length: Box::new(length),
            },
        }
    }

    pub fn lst_sub<I, J>(self, start: I, length: J) -> Self
    where
        I: Into<BigInt> + Clone,
        J: Into<BigInt> + Clone,
    {
        let start: BigInt = start.clone().into();
        let length: BigInt = length.clone().into();
        let start_us: Result<usize, _> = start.clone().try_into();
        let length_us: Result<usize, _> = length.clone().try_into();
        match (self, start_us, length_us) {
            (Expr::EList(vec), Ok(start), Ok(length)) => {
                let result = vec.into_iter().skip(start).take(length).collect::<Vec<_>>();
                if result.len() != length {
                    panic!("ListSub is invalid!");
                }
                Expr::EList(result)
            }
            (Expr::Lit(Literal::LList(vec)), Ok(start), Ok(length)) => {
                let result: Vec<_> = vec
                    .into_iter()
                    .skip(start)
                    .take(length)
                    .map(Expr::from)
                    .collect();
                if result.len() != length {
                    panic!("ListSub is invalid!");
                }
                Expr::EList(result)
            }
            (x, _, _) => Self::LstSub {
                list: Box::new(x),
                start: Box::new(Expr::int(start)),
                length: Box::new(Expr::int(length)),
            },
        }
    }

    pub fn lst_len(self) -> Self {
        match self {
            Expr::EList(vec) => Expr::int(vec.len()),
            Expr::Lit(Literal::LList(vec)) => Expr::int(vec.len()),
            _ => Expr::UnOp {
                operator: UnOp::LstLen,
                operand: Box::new(self),
            },
        }
    }

    pub fn eq_expr(e1: Expr, e2: Expr) -> Self {
        Expr::BinOp {
            operator: BinOp::Equal,
            left_operand: Box::new(e1),
            right_operand: Box::new(e2),
        }
    }

    pub fn eq_f<E: Into<Expr>>(self, e2: E) -> super::Formula {
        super::Formula::eq(self, e2.into())
    }

    pub fn lst_concat(self, e2: Expr) -> Self {
        match (self, e2) {
            (Expr::EList(mut vec1), Expr::EList(mut vec2)) => {
                vec1.append(&mut vec2);
                Expr::EList(vec1)
            }
            (Expr::Lit(Literal::LList(mut vec1)), Expr::Lit(Literal::LList(mut vec2))) => {
                vec1.append(&mut vec2);
                Expr::Lit(Literal::LList(vec1))
            }
            (Expr::EList(vec), x) | (x, Expr::EList(vec)) if vec.is_empty() => x,
            (x, Expr::Lit(Literal::LList(vec))) | (Expr::Lit(Literal::LList(vec)), x)
                if vec.is_empty() =>
            {
                x
            }
            (e1, e2) => Self::NOp {
                operator: NOp::LstCat,
                operands: vec![e1, e2],
            },
        }
    }

    pub fn lst_head(self) -> Self {
        match self {
            Expr::EList(vec) => {
                if vec.is_empty() {
                    panic!("lst_head on empty list");
                }
                vec[0].clone()
            }
            s => Self::UnOp {
                operator: UnOp::Car,
                operand: Box::new(s),
            },
        }
    }

    pub fn lst_tail(self) -> Self {
        match self {
            Expr::EList(mut vec) => {
                if vec.is_empty() {
                    panic!("lst_head on empty list");
                }
                vec.remove(0);
                Expr::EList(vec)
            }
            s => Self::UnOp {
                operator: UnOp::Cdr,
                operand: Box::new(s),
            },
        }
    }

    pub fn plus(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::int(i + j),
            _ => Expr::BinOp {
                operator: BinOp::IPlus,
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
            },
        }
    }

    pub fn fplus(e1: Expr, e2: Expr) -> Self {
        Expr::BinOp {
            operator: BinOp::FPlus,
            left_operand: Box::new(e1),
            right_operand: Box::new(e2),
        }
    }

    pub fn minus(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Int(i)), Expr::Lit(Literal::Int(j))) => Expr::int(i - j),
            _ => Expr::BinOp {
                operator: BinOp::IMinus,
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
            },
        }
    }

    pub fn fminus(e1: Expr, e2: Expr) -> Self {
        Expr::BinOp {
            operator: BinOp::FMinus,
            left_operand: Box::new(e1),
            right_operand: Box::new(e2),
        }
    }

    pub fn and(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Bool(i)), Expr::Lit(Literal::Bool(j))) => Expr::bool(*i && *j),
            _ => Expr::BinOp {
                operator: BinOp::BAnd,
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
            },
        }
    }

    pub fn or(e1: Expr, e2: Expr) -> Self {
        match (&e1, &e2) {
            (Expr::Lit(Literal::Bool(i)), Expr::Lit(Literal::Bool(j))) => Expr::bool(*i || *j),
            _ => Expr::BinOp {
                operator: BinOp::BOr,
                left_operand: Box::new(e1),
                right_operand: Box::new(e2),
            },
        }
    }

    pub fn undefined() -> Self {
        Self::Lit(Literal::Undefined)
    }

    pub fn subst_pvar(&mut self, mapping: &HashMap<String, Expr>) {
        let mut visitor = super::visitors::SubstPVar::new(mapping);
        visitor.visit_expr(self);
    }
}

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for &'a Expr
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        match self {
            Expr::Lit(lit) => lit.pretty(alloc),
            Expr::PVar(var) | Expr::LVar(var) | Expr::ALoc(var) => alloc.text(var),
            Expr::UnOp { operator, operand } => operator
                .pretty(alloc)
                .append(alloc.space())
                .append(operand.pretty(alloc)),
            Expr::BinOp {
                operator,
                left_operand,
                right_operand,
            } => match operator {
                BinOp::LstNth | BinOp::StrNth | BinOp::LstRepeat => {
                    alloc.text(operator.to_string()).append(
                        left_operand
                            .pretty(alloc)
                            .append(alloc.text(", "))
                            .append(right_operand.pretty(alloc))
                            .parens(),
                    )
                }

                _ => left_operand
                    .pretty(alloc)
                    .parens()
                    .append(alloc.space())
                    .append(operator.pretty(alloc))
                    .append(alloc.space())
                    .append(right_operand.pretty(alloc).parens())
                    .parens(),
            },
            Expr::LstSub {
                list,
                start,
                length,
            } => alloc.text("l-sub").append(
                alloc
                    .intersperse([&**list, &**start, &**length], ", ")
                    .parens(),
            ),
            Expr::EList(vec) => docs![
                alloc,
                alloc.space(),
                alloc.intersperse(vec, ", "),
                alloc.space()
            ]
            .enclose("{{", "}}"),
            Expr::ESet(vec) => alloc
                .text("-{ ")
                .append(alloc.intersperse(vec, ", "))
                .append(alloc.text(" }-")),
            Expr::NOp { operator, operands } => operator
                .pretty(alloc)
                .append(alloc.intersperse(operands, ", ").parens()),
            Expr::EExists(vars, body) => {
                let vars = alloc.intersperse(
                    vars.iter().map(|(v, ty)| {
                        alloc.text(format!("#{v}")).append(
                            ty.map(|ty| alloc.text(" : ").append(ty.pretty(alloc)))
                                .unwrap_or(alloc.nil()),
                        )
                    }),
                    ", ",
                );

                docs![
                    alloc,
                    "exists",
                    alloc.space(),
                    vars,
                    ".",
                    alloc.space(),
                    &**body
                ]
            }
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let alloc = pretty::Arena::new();
        self.pretty(&alloc).render_fmt(80, f)
    }
}
