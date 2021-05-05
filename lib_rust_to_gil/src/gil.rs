use std::collections::HashMap;

pub type LVar = String;

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
pub enum NOp {
    LstCat,
    SetUnion,
    SetInter,
}

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
pub struct Bindings {
    name: String,
    binds: Vec<(String, Expr)>,
}

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
pub struct SinglePhiAssignment {
    variable: String,
    values: Vec<Expr>,
}

#[derive(Debug)]
pub enum Cmd {
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
    Goto(String),
    GuardedGoto {
        guard: Expr,
        then_branch: String,
        else_branch: String,
    },
    Call {
        variable: String,
        proc_ident: Expr,
        parameters: Vec<Expr>,
        error_lab: Option<String>,
        bindings: Bindings,
    },
    ECall {
        variable: String,
        proc_ident: Expr,
        parameters: Vec<Expr>,
        error_lab: Option<String>,
    },
    Apply {
        variable: String,
        args: Expr,
        error_lab: Option<String>,
    },
    PhiAssignment(Vec<SinglePhiAssignment>),
    ReturnNormal,
    ReturnError,
    Fail {
        name: String,
        parameters: Vec<Expr>,
    },
}

#[derive(Debug)]
pub enum Flag {
    Normal,
    Error,
}

#[derive(Debug)]
pub struct DefinitionLabel {
    name: String,
    existentials: Vec<String>,
}

#[derive(Debug)]
pub struct PredDefinition {
    lab_opt: Option<DefinitionLabel>,
    assertion: Assertion,
}

#[derive(Debug)]
pub struct Pred {
    pred_name: String,
    pred_num_params: i32,
    pred_params: Vec<(String, Option<Type>)>,
    pred_ins: Vec<i32>,
    pred_definitions: Vec<PredDefinition>,
    pred_pure: bool,
    pred_normalised: bool,
}

#[derive(Debug)]
pub struct Lemma {
    lemma_name: String,
    lemma_params: Vec<String>,
    lemma_hyp: Assertion,
    lemma_concs: Vec<Assertion>,
    lemma_variant: Option<Expr>,
    lemma_existentials: Vec<String>,
}

#[derive(Debug)]
pub struct SingleSpec {
    ss_pre: Assertion,
    ss_posts: Vec<Assertion>,
    ss_flag: Flag,
    ss_to_verify: bool,
    ss_label: Option<DefinitionLabel>,
}

#[derive(Debug)]
pub struct Spec {
    spec_name: String,
    spec_params: Vec<String>,
    spec_sspecs: Vec<SingleSpec>,
    spec_normalised: bool,
    spec_to_verify: bool,
}

#[derive(Debug)]
pub struct BiSpec {
    bispec_name: String,
    bispec_params: Vec<String>,
    bispec_pres: Vec<Assertion>,
    bispec_normalised: bool,
}

#[derive(Debug)]
pub struct Macro {
    macro_name: String,
    macro_params: Vec<String>,
    macro_definition: Vec<LCmd>,
}

#[derive(Debug)]
pub struct Position {
    pos_line: i32,
    pos_column: i32
}

impl Default for Position{
    fn default() -> Self {
        Position {
            pos_line: -1,
            pos_column: -1
        }
    }
}

#[derive(Debug)]
pub struct Location {
    loc_start : Position,
    loc_end : Position,
    loc_source : String
}

impl Default for Location {
    fn default() -> Self {
        Location {
            loc_start: Position::default(),
            loc_end: Position::default(),
            loc_source: "(none)".to_string()
        }
    }
}

#[derive(Debug)]
pub struct Annot {
    origin_loc: Location,
    loop_info:  Vec<String>, 
}

#[derive(Debug)]
pub struct ProcBodyItem {
    annot: Annot,
    label: Option<String>,
    cmd: Cmd,
}

#[derive(Debug, Default)]
pub struct Proc {
    proc_name: String,
    proc_body: Vec<ProcBodyItem>,
    proc_params: Vec<String>,
    proc_spec: Option<Spec>,
}

impl Proc {
    pub fn new(proc_name: String) -> Self {
        Proc {
            proc_name,
            .. Proc::default()
        }
    }
}

#[derive(Debug)]
pub struct Import {
    path: String,
    verify: bool,
}

#[derive(Default, Debug)]
pub struct Prog {
    imports: Vec<Import>,
    lemmas: HashMap<String, Lemma>,
    preds: HashMap<String, Pred>,
    only_specs: HashMap<String, Spec>,
    procs: HashMap<String, Proc>,
    macros: HashMap<String, Macro>,
    bi_specs: HashMap<String, BiSpec>,
    proc_names: Vec<String>,
}
