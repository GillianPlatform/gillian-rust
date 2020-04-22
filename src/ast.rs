use std::collections::HashMap;

pub type LVar = String;

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

pub enum Type {
    UndefinedType,
    NullType,
    EmptyType,
    NoneType,
    BooleanType,
    IntType,
    NumberType,
    StringType,
    ObjectType,
    ListType,
    TypeType,
    SetType,
}

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
    StrCat,
    StrNth,
    SetDiff,
    BSetMem,
    BSetSub,
}

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

pub enum NOp {
    LstCat,
    SetUnion,
    SetInter,
}

pub enum Literal {
    Undefined,
    Null,
    Empty,
    Constant(Constant),
    Bool(bool),
    Int(i64),
    Num(f32),
    String(String),
    Loc(String),
    Type(Type),
    LList(Vec<Literal>),
    Nono,
}

pub enum Expr {
    Lit(Literal),
    PVar(String),
    LVar(LVar),
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
        operator: BinOp,
        operands: Vec<Expr>,
    },
    LstSub {
        list: Box<Expr>,
        start: Box<Expr>,
        end: Box<Expr>,
    },
    EList(Vec<Expr>),
    ESet(Vec<Expr>),
}

pub enum Formula {
    True,
    False,
    Not(Box<Formula>),
    And {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    Or {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    Eq {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Less {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    LessEq {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    StrLess {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    SetMem {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    SetSub {
        left: Box<Formula>,
        right: Box<Formula>,
    },
    ForAll {
        quantified: Vec<(String, Option<Type>)>,
        formula: Box<Formula>,
    },
}

pub enum Assertion {
    Emp,
    Star {
        left: Box<Assertion>,
        right: Box<Assertion>,
    },
    Pred {
        name: String,
        params: Vec<Expr>,
    },
    Pure(Formula),
    Types(Vec<(Expr, Type)>),
    GA {
        name: String,
        ins: Vec<Expr>,
        outs: Vec<Expr>,
    },
}

pub struct Bindings {
    name: String,
    binds: Vec<(String, Expr)>,
}

pub enum SLCmd {
    Fold {
        pred_name: String,
        parameters: Vec<Expr>,
        bindings: Bindings,
    },
    Unfold {
        pred_name: String,
        parameters: Vec<Expr>,
        bindings: Bindings,
        rec: bool,
    },
    GUnfold(String),
    ApplyLem {
        lemma_name: String,
        parameters: Vec<Expr>,
        existentials: Vec<String>,
    },
    SepAssert {
        assertion: Assertion,
        existentials: Vec<String>,
    },
    Invariant {
        assertion: Assertion,
        existentials: Vec<String>,
    },
}

pub enum LCmd {
    If {
        guard: Expr,
        then_branch: Box<LCmd>,
        else_branch: Box<LCmd>,
    },
    Branch(Formula),
    Macro {
        macro_name: String,
        parameters: Vec<Expr>,
    },
    Assert(Formula),
    Assume(Formula),
    AssumeType {
        variable: String,
        typ: Type,
    },
    SpecVar(Vec<String>),
    SL(SLCmd),
}

pub struct SinglePhiAssignment {
    variable: String,
    values: Vec<Expr>,
}

pub enum Cmd<L> {
    Skip,
    Assignment {
        variable: String,
        assigned_expr: Expr,
    },
    Action {
        variable: String,
        action_name: String,
        parameters: Vec<Expr>,
    },
    Logic(LCmd),
    Goto(L),
    GuardedGoto {
        guard: Expr,
        then_branch: L,
        else_branch: L,
    },
    Call {
        variable: String,
        proc_ident: Expr,
        parameters: Vec<Expr>,
        error_lab: Option<L>,
        bindings: Bindings,
    },
    ECall {
        variable: String,
        proc_ident: Expr,
        parameters: Vec<Expr>,
        error_lab: Option<L>,
    },
    Apply {
        variable: String,
        args: Expr,
        error_lab: Option<L>,
    },
    PhiAssignment(Vec<SinglePhiAssignment>),
    ReturnNormal,
    ReturnError,
    Fail {
        name: String,
        parameters: Vec<Expr>,
    },
}

pub enum Flag {
    Normal,
    Error,
}

pub struct DefinitionLabel {
    name: String,
    existentials: Vec<String>,
}

pub struct PredDefinition {
    lab_opt: Option<DefinitionLabel>,
    assertion: Assertion,
}

pub struct Pred {
    pred_name: String,
    pred_num_params: i32,
    pred_params: Vec<(String, Option<Type>)>,
    pred_ins: Vec<i32>,
    pred_definitions: Vec<PredDefinition>,
    pred_pure: bool,
    pred_normalised: bool,
}

pub struct Lemma {
    lemma_name: String,
    lemma_params: Vec<String>,
    lemma_hyp: Assertion,
    lemma_concs: Vec<Assertion>,
    lemma_variant: Option<Expr>,
    lemma_existentials: Vec<String>,
}

pub struct SingleSpec {
    ss_pre: Assertion,
    ss_posts: Vec<Assertion>,
    ss_flag: Flag,
    ss_to_verify: bool,
    ss_label: Option<DefinitionLabel>,
}

pub struct Spec {
    spec_name: String,
    spec_params: Vec<String>,
    spec_sspecs: Vec<SingleSpec>,
    spec_normalised: bool,
    spec_to_verify: bool,
}

pub struct BiSpec {
    bispec_name: String,
    bispec_params: Vec<String>,
    bispec_pres: Vec<Assertion>,
    bispec_normalised: bool,
}

pub struct Macro {
    macro_name: String,
    macro_params: Vec<String>,
    macro_definition: Vec<LCmd>,
}

pub struct ProcBodyItem<A, L> {
    annot: A,
    label: Option<L>,
    cmd: Cmd<L>,
}

pub struct Proc<A, L> {
    proc_name: String,
    proc_body: Vec<ProcBodyItem<A, L>>,
    proc_params: Vec<String>,
    proc_spec: Option<Spec>,
}

pub struct Import {
    path: String,
    verify: bool,
}

pub struct Prog<A, L> {
    imports: Vec<Import>,
    lemmas: HashMap<String, Lemma>,
    preds: HashMap<String, Pred>,
    only_specs: HashMap<String, Spec>,
    procs: HashMap<String, Proc<A, L>>,
    macros: HashMap<String, Macro>,
    bi_specs: HashMap<String, BiSpec>,
    proc_names: Vec<String>,
}
