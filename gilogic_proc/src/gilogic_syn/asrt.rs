use syn::{punctuated::Punctuated, token::Paren, *};

use super::subst::VarSubst;

use proc_macro2::{Span, TokenStream};

use quote::IdentFragment;
use std::collections::HashMap;
use std::fmt::{self, Display};
use std::hash::{Hash, Hasher};
use std::mem;

pub mod kw {
    syn::custom_keyword!(emp);
    syn::custom_keyword!(forall);
    syn::custom_keyword!(exists);
    syn::custom_keyword!(requires);
    syn::custom_keyword!(ensures);
    syn::custom_keyword!(model);
    syn::custom_keyword!(assuming);
    syn::custom_keyword!(from);
    syn::custom_keyword!(extract);
    syn::custom_keyword!(prophecise);
}

#[allow(dead_code)]
pub struct Specification {
    pub forall: Option<kw::forall>,
    pub lvars: Punctuated<LvarDecl, Token![,]>,
    pub dot: Option<Token![.]>,
    pub requires: kw::requires,
    pub precond: Punctuated<AsrtFragment, Token![*]>,
    pub postconds: Vec<SpecEnsures>,
}

#[allow(dead_code)]
pub struct SpecEnsures {
    pub exists: Option<kw::exists>,
    pub rvars: Punctuated<LvarDecl, Token![,]>,
    pub dot2: Option<Token![.]>,
    pub ensures: kw::ensures,
    pub postcond: Punctuated<AsrtFragment, Token![*]>,
}

#[derive(Debug)]
pub struct Assertion {
    pub pipe1: Option<Token![|]>,
    pub lvars: Punctuated<LvarDecl, Token![,]>,
    pub pipe2: Option<Token![|]>,
    pub def: Punctuated<AsrtFragment, Token![*]>,
}

#[derive(Debug, Clone)]
pub struct LvarDecl {
    pub ident: Ident,
    pub ty_opt: Option<(Token![:], Type)>,
}

impl From<(Ident, Type)> for LvarDecl {
    fn from((ident, ty): (Ident, Type)) -> Self {
        Self {
            ident,
            ty_opt: Some((Token![:](Span::call_site()), ty)),
        }
    }
}

impl From<Ident> for LvarDecl {
    fn from(ident: Ident) -> Self {
        Self {
            ident,
            ty_opt: None,
        }
    }
}

ast_enum_of_structs! {
  /// A Gilogic assertion
  pub enum AsrtFragment {
    /// The `emp` separation logic assertion
    Emp(AsrtEmp),
    /// The `->` separation logic assertion
    PointsTo(AsrtPointsTo),
    /// A predicate call
    PredCall(AsrtPredCall),
    /// A pure formula
    Pure(Formula),
    /// A pure observation
    Observation(Observation),
  }
}

ast_struct! {
  /// The assertion `emp`
  pub struct AsrtEmp {
    pub emp_token: kw::emp,
  }
}

ast_struct! {
  /// `e -> v`
  pub struct AsrtPointsTo {
    pub paren_token: Paren,
    pub left: Term,
    pub dash_token: Token![-],
    pub gt_token: Token![>],
    pub right: Term,
  }
}

ast_enum! {
  /// A predicate call. Either `x.pred(args)`, or `pred(args)`
  #[derive(Debug)]
  pub enum AsrtPredCall {
    /// A simple call, e.g. `pred(args)`
    SimpleCall(TermCall),
    /// A method call, e.g. `x.pred(args)`
    MethodCall(TermMethodCall),
  }
}

impl AsrtPredCall {
    pub fn args(&self) -> &Punctuated<Term, syn::token::Comma> {
        match self {
            Self::SimpleCall(term_call) => &term_call.args,
            Self::MethodCall(method_call) => &method_call.args,
        }
    }

    pub fn args_mut(&mut self) -> &mut Punctuated<Term, syn::token::Comma> {
        match self {
            Self::SimpleCall(term_call) => &mut term_call.args,
            Self::MethodCall(method_call) => &mut method_call.args,
        }
    }
}

ast_struct! {
  pub struct Formula {
    pub paren_token: Paren,

    // A formula is a term that has to be a valid formula.
    // Pre-typing will check for valid operators.
    pub inner: Term,
  }
}

impl Formula {
    pub fn from_term(term: Term) -> Self {
        Self {
            paren_token: Paren::default(),
            inner: term,
        }
    }
}

ast_struct! {
    /// A prophetic assertion. $ assert $
    pub struct Observation {
        pub open_dollar: Token![$],
        pub inner: Term,
        pub close_dollar: Token![$],
    }
}

ast_enum_of_structs! {
    /// A Gilogic expression term.
    ///
    /// For information about Syn enums, consult [syn::Expr]
    pub enum Term {
        /// A slice literal term: `[a, b, c, d]`.
        Array(TermArray),

        /// A binary operation: `a + b`, `a * b`.
        Binary(TermBinary),

        /// A blocked scope: `{ ... }`.
        Block(TermBlock),

        /// A function call term: `invoke(a, b)`.
        Call(TermCall),

        /// A cast term: `foo as f64`.
        Cast(TermCast),

        /// Access of a named struct field (`obj.k`) or unnamed tuple struct
        /// field (`obj.0`).
        Field(TermField),

        // Universal quantification
        Forall(TermForall),

        // Existential quantification
        Exists(TermExists),

        /// An term contained within invisible delimiters.
        ///
        /// This variant is important for faithfully representing the precedence
        /// of expressions and is related to `None`-delimited spans in a
        /// `TokenStream`.
        Group(TermGroup),

        /// An `if` term with an optional `else` block: `if expr { ... }
        /// else { ... }`.
        ///
        /// The `else` branch term may only be an `If` or `Block`
        /// term, not any of the other types of term.
        If(TermIf),

        // Implication
        Impl(TermImpl),

        /// A square bracketed indexing term: `vector[2]`.
        Index(TermIndex),

        /// A `let` guard: `let Some(x) = opt`.
        Let(TermLet),

        /// A literal in place of an term: `1`, `"foo"`.
        Lit(TermLit),

        /// A `match` term: `match n { Some(n) => {}, None => {} }`.
        Match(TermMatch),

        /// A method call term: `x.foo::<T>(a, b)`.
        MethodCall(TermMethodCall),

        /// A parenthesized term: `(a + b)`.
        Paren(TermParen),

        /// A path like `std::mem::replace` possibly containing generic
        /// parameters and a qualified self-type.
        ///
        /// A plain identifier like `x` is a path of length 1.
        Path(TermPath),

        /// A range term: `1..2`, `1..`, `..2`, `1..=2`, `..=2`.
        Range(TermRange),

        Reference(TermReference),

        /// An array literal constructed from one repeated element: `[0u8; N]`.
        Repeat(TermRepeat),

        /// A struct literal term: `Point { x: 1, y: 1 }`.
        ///
        /// The `rest` provides the value of the remaining fields as in `S { a:
        /// 1, b: 1, ..rest }`.
        Struct(TermStruct),

        /// A tuple term: `(a, b, c, d)`.
        Tuple(TermTuple),

        /// A type ascription term: `foo: f64`.
        Type(TermType),

        /// A unary operation: `!x`, `*x`.
        Unary(TermUnary),

        /// Tokens in term position not interpreted by Syn.
        Verbatim(TokenStream),

        /// A macro invocation expression: `format!("{}", q)`.
        Macro(ExprMacro),

        /// A closure expresion: |a, b| a + b.
        Closure(TermClosure),

        /// A logical variable #x
        // LogVar(TermLogVar),

        #[doc(hidden)]
        __Nonexhaustive,
    }
}

ast_struct! {
    /// A braced block containing Pearlite statements.
    pub struct TBlock {
        pub brace_token: token::Brace,
        /// Statements in a block
        pub stmts: Vec<TermStmt>,
    }
}

ast_enum! {
    /// A statement, usually ending in a semicolon.
    #[derive(Debug)]
    pub enum TermStmt {
        /// A local (let) binding.
        Local(TLocal),

        /// An item definition.
        Item(Item),

        /// Expr without trailing semicolon.
        Expr(Term),

        /// Expression with trailing semicolon.
        Semi(Term, Token![;]),
    }
}

ast_struct! {
    /// A local `let` binding: `let x: u64 = s.parse()?`.
    pub struct TLocal {
        pub let_token: Token![let],
        pub pat: Pat,
        pub init: Option<(Token![=], Box<Term>)>,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// A slice literal term: `[a, b, c, d]`.
    pub struct TermArray {
        pub bracket_token: token::Bracket,
        pub elems: Punctuated<Term, Token![,]>,
    }
}

ast_struct! {
    /// A binary operation: `a + b`, `a * b`.
    pub struct TermBinary {
        pub left: Box<Term>,
        pub op: BinOp,
        pub right: Box<Term>,
    }
}

ast_struct! {
    /// A blocked scope: `{ ... }`.
    pub struct TermBlock  {
        pub label: Option<Label>,
        pub block: TBlock,
    }
}

ast_struct! {
    /// A function call term: `invoke(a, b)`.
    pub struct TermCall {
        pub func: Box<Term>,
        pub paren_token: token::Paren,
        pub args: Punctuated<Term, Token![,]>,
    }
}

ast_struct! {
    /// A cast term: `foo as f64`.
    pub struct TermCast {
        pub expr: Box<Term>,
        pub as_token: Token![as],
        pub ty: Box<Type>,
    }
}

ast_struct! {
    /// A closure expression: `|a, b| a + b`.
    pub struct TermClosure  {
        pub attrs: Vec<Attribute>,
        pub or1_token: Token![|],
        pub inputs: Punctuated<Pat, Token![,]>,
        pub or2_token: Token![|],
        pub output: ReturnType,
        pub body: Box<Term>,
    }
}

ast_struct! {
    /// Access of a named struct field (`obj.k`) or unnamed tuple struct
    /// field (`obj.0`).
    pub struct TermField {
        pub base: Box<Term>,
        pub dot_token: Token![.],
        pub member: Member,
    }
}

ast_struct! {
    /// An term contained within invisible delimiters.
    ///
    /// This variant is important for faithfully representing the precedence
    /// of expressions and is related to `None`-delimited spans in a
    /// `TokenStream`.
    pub struct TermGroup  {
        pub group_token: token::Group,
        pub expr: Box<Term>,
    }
}

ast_struct! {
    /// An `if` term with an optional `else` block: `if expr { ... }
    /// else { ... }`.
    ///
    /// The `else` branch term may only be an `If` or `Block`
    /// term, not any of the other types of term.
    pub struct TermIf  {
        pub if_token: Token![if],
        pub cond: Box<Term>,
        pub then_branch: TBlock,
        pub else_branch: Option<(Token![else], Box<Term>)>,
    }
}

ast_struct! {
    /// A square bracketed indexing term: `vector[2]`.
    pub struct TermIndex {
        pub expr: Box<Term>,
        pub bracket_token: token::Bracket,
        pub index: Box<Term>,
    }
}

ast_struct! {
    /// A `let` guard: `let Some(x) = opt`.
    pub struct TermLet  {
        pub let_token: Token![let],
        pub pat: Pat,
        pub eq_token: Token![=],
        pub expr: Box<Term>,
    }
}

ast_struct! {
    /// A literal in place of an term: `1`, `"foo"`.
    pub struct TermLit {
        pub lit: Lit,
    }
}

ast_struct! {
    /// A `match` term: `match n { Some(n) => {}, None => {} }`.
    pub struct TermMatch  {
        pub match_token: Token![match],
        pub expr: Box<Term>,
        pub brace_token: token::Brace,
        pub arms: Vec<TermArm>,
    }
}

ast_struct! {
    /// A method call term: `x.foo::<T>(a, b)`.
    pub struct TermMethodCall  {
        pub receiver: Box<Term>,
        pub dot_token: Token![.],
        pub method: Ident,
        pub turbofish: Option<TermMethodTurbofish>,
        pub paren_token: token::Paren,
        pub args: Punctuated<Term, Token![,]>,
    }
}

ast_struct! {
    /// A parenthesized term: `(a + b)`.
    pub struct TermParen {
        pub paren_token: token::Paren,
        pub expr: Box<Term>,
    }
}

ast_struct! {
    /// A path like `std::mem::replace` possibly containing generic
    /// parameters and a qualified self-type.
    ///
    /// A plain identifier like `x` is a path of length 1.
    pub struct TermPath {
        pub inner: ExprPath,
        // pub qself: Option<QSelf>,
        // pub path: Path,
    }
}

ast_struct! {
    /// A range term: `1..2`, `1..`, `..2`, `1..=2`, `..=2`.
    pub struct TermRange  {
        pub from: Option<Box<Term>>,
        pub limits: RangeLimits,
        pub to: Option<Box<Term>>,
    }
}

ast_struct! {
    pub struct TermReference {
        // pub attrs: Vec<Attribute>,
        pub and_token: Token![&],
        pub mutability: Option<Token![mut]>,
        pub term: Box<Term>,
    }
}

ast_struct! {
    /// An array literal constructed from one repeated element: `[0u8; N]`.
    pub struct TermRepeat  {
        pub bracket_token: token::Bracket,
        pub expr: Box<Term>,
        pub semi_token: Token![;],
        pub len: Box<Term>,
    }
}

ast_struct! {
    /// A struct literal term: `Point { x: 1, y: 1 }`.
    ///
    /// The `rest` provides the value of the remaining fields as in `S { a:
    /// 1, b: 1, ..rest }`.
    pub struct TermStruct  {
        pub path: Path,
        pub brace_token: token::Brace,
        pub fields: Punctuated<TermFieldValue, Token![,]>,
        pub dot2_token: Option<Token![..]>,
        pub rest: Option<Box<Term>>,
    }
}

ast_struct! {
    /// A tuple term: `(a, b, c, d)`.
    pub struct TermTuple  {
        pub paren_token: token::Paren,
        pub elems: Punctuated<Term, Token![,]>,
    }
}

impl TermTuple {
    pub fn unit() -> Self {
        Self {
            paren_token: token::Paren::default(),
            elems: Punctuated::new(),
        }
    }
}

ast_struct! {
    /// A type ascription term: `foo: f64`.
    pub struct TermType  {
        pub expr: Box<Term>,
        pub colon_token: Token![:],
        pub ty: Box<Type>,
    }
}

ast_struct! {
    pub struct QuantArg {
        pub ident: Ident,
        pub colon_token: Token![:],
        pub ty: Box<Type>,
    }
}

ast_struct! {
    pub struct TermForall {
        pub forall_token: kw::forall,
        pub lt_token: Token![<],
        pub args: Punctuated<QuantArg, Token![,]>,
        pub gt_token: Token![>],
        pub term: Box<Term>
    }
}

ast_struct! {
    pub struct TermExists {
        pub exists_token: kw::exists,
        pub lt_token: Token![<],
        pub args: Punctuated<QuantArg, Token![,]>,
        pub gt_token: Token![>],
        pub term: Box<Term>
    }
}

ast_struct! {
    pub struct TermImpl {
        pub hyp: Box<Term>,
        pub eqeq_token: Token![==],
        pub gt_token: Token![>],
        pub cons: Box<Term>,
    }
}

ast_struct! {
    /// A unary operation: `!x`, `*x`.
    pub struct TermUnary {
        pub op: UnOp,
        pub expr: Box<Term>,
    }
}

ast_struct! {
    /// The index of an unnamed tuple struct field.
    pub struct Index {
        pub index: u32,
        pub span: Span,
    }
}

impl From<usize> for Index {
    fn from(index: usize) -> Index {
        assert!(index < u32::max_value() as usize);
        Index {
            index: index as u32,
            span: Span::call_site(),
        }
    }
}

impl Eq for Index {}

impl PartialEq for Index {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl Hash for Index {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.index.hash(state);
    }
}

impl IdentFragment for Index {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(&self.index, formatter)
    }

    fn span(&self) -> Option<Span> {
        Some(self.span)
    }
}

ast_struct! {
    /// The `::<>` explicit type parameters passed to a method call:
    /// `parse::<u64>()`.
    pub struct TermMethodTurbofish {
        pub colon2_token: Token![::],
        pub lt_token: Token![<],
        pub args: Punctuated<TermGenericMethodArgument, Token![,]>,
        pub gt_token: Token![>],
    }
}

ast_enum! {
    /// An individual generic argument to a method, like `T`.
    ///
    #[derive(Debug)]
    pub enum TermGenericMethodArgument {
        /// A type argument.
        Type(Type),
        /// A const term. Must be inside of a block.
        ///
        /// NOTE: Identity expressions are represented as Type arguments, as
        /// they are indistinguishable syntactically.
        Const(Term),
    }
}

ast_struct! {
    /// A field-value pair in a struct literal.
    pub struct TermFieldValue {
        /// Attributes tagged on the field.

        /// Name or index of the field.
        pub member: Member,

        /// The colon in `Struct { x: x }`. If written in shorthand like
        /// `Struct { x }`, there is no colon.
        pub colon_token: Option<Token![:]>,

        /// Value of the field.
        pub expr: Term,
    }
}

ast_struct! {
    /// One arm of a `match` term: `0...10 => { return true; }`.
    ///
    /// As in:
    ///
    /// ```
    /// # fn f() -> bool {
    /// #     let n = 0;
    /// match n {
    ///     0..=10 => {
    ///         return true;
    ///     }
    ///     // ...
    ///     # _ => {}
    /// }
    /// #   false
    /// # }
    /// ```
    pub struct TermArm {
        pub pat: Pat,
        pub guard: Option<(Token![if], Box<Term>)>,
        pub fat_arrow_token: Token![=>],
        pub body: Box<Term>,
        pub comma: Option<Token![,]>,
    }
}

pub(crate) fn requires_terminator(expr: &Term) -> bool {
    // see https://github.com/rust-lang/rust/blob/2679c38fc/src/librustc_ast/util/classify.rs#L7-L25
    matches!(expr, Term::Block(..) | Term::If(..) | Term::Match(..))
}

pub(crate) mod parsing {
    use super::*;
    use proc_macro2::Delimiter;
    use syn::parse::{discouraged::AnyDelimiter, Parse, ParseStream, Result};
    // use syn::path;
    use std::cmp::Ordering;

    impl Parse for LvarDecl {
        fn parse(input: ParseStream) -> Result<Self> {
            let ident = input.parse()?;
            let ty_opt = if input.peek(Token![:]) {
                let colon = input.parse()?;
                let ty = input.parse()?;
                Some((colon, ty))
            } else {
                None
            };
            Ok(LvarDecl { ident, ty_opt })
        }
    }

    impl Parse for Specification {
        fn parse(input: ParseStream) -> Result<Self> {
            let lookahead = input.lookahead1();
            let (forall, lvars, dot) = if lookahead.peek(kw::forall) {
                let forall = input.parse::<kw::forall>()?;
                let lvars = Punctuated::parse_separated_nonempty(input)?;
                let dot = input.parse()?;
                (Some(forall), lvars, Some(dot))
            } else {
                (None, Punctuated::new(), None)
            };

            let requires = input.parse()?;

            let content;
            let _ = braced!(content in input);
            let precond = Punctuated::parse_separated_nonempty(&content)?;

            let mut postconds = Vec::new();

            while !input.is_empty() {
                postconds.push(input.parse()?);
            }

            Ok(Specification {
                forall,
                lvars,
                dot,
                requires,
                precond,
                postconds,
            })
        }
    }
    impl Parse for SpecEnsures {
        fn parse(input: ParseStream) -> Result<Self> {
            let lookahead = input.lookahead1();
            let (exists, rvars, dot2) = if lookahead.peek(kw::exists) {
                let exists = input.parse::<kw::exists>()?;
                let lvars = Punctuated::parse_separated_nonempty(input)?;
                let dot = input.parse()?;
                (Some(exists), lvars, Some(dot))
            } else {
                (None, Punctuated::new(), None)
            };

            let ensures = input.parse()?;
            let content;
            let _ = braced!(content in input);
            let postcond = Punctuated::parse_separated_nonempty(&content)?;
            Ok(SpecEnsures {
                exists,
                rvars,
                dot2,
                ensures,
                postcond,
            })
        }
    }

    impl Parse for Assertion {
        fn parse(input: ParseStream) -> Result<Self> {
            let mut lvars = Punctuated::new();
            let (pipe1, pipe2) = if input.peek(Token![|]) {
                let pipe1 = input.parse()?;
                loop {
                    if input.peek(Token![|]) {
                        break;
                    }
                    let value = input.parse()?;
                    lvars.push_value(value);
                    if input.peek(Token![|]) {
                        break;
                    }
                    let punct: Token![,] = input.parse()?;
                    lvars.push_punct(punct);
                }
                (Some(pipe1), Some(input.parse()?))
            } else {
                (None, None)
            };
            let def = Punctuated::parse_separated_nonempty(input)?;
            Ok(Self {
                pipe1,
                lvars,
                pipe2,
                def,
            })
        }
    }

    impl Parse for AsrtFragment {
        fn parse(input: ParseStream) -> Result<Self> {
            if input.peek(kw::emp) {
                return input.parse().map(Self::Emp);
            }
            if input.peek(token::Dollar) {
                // We're in the case of an observation.
                let open_dollar = input.parse()?;
                let inner = input.parse()?;
                let close_dollar = input.parse()?;
                return Ok(Self::Observation(Observation {
                    open_dollar,
                    inner,
                    close_dollar,
                }));
            }
            if input.peek(token::Paren) {
                // We're in the case of either a formula or a points-to.
                // We start by parsing a term, and if we find a points-to pair of tokens,
                // we interpret as a pointso, otherwise, it's intepreted as a formula.

                let inner;
                let paren_token = parenthesized!(inner in input);

                let left = inner.parse()?;
                return if inner.peek(Token![-]) && inner.peek2(Token![>]) {
                    let dash_token = inner.parse()?;
                    let gt_token = inner.parse()?;
                    let right = inner.parse()?;
                    Ok(Self::PointsTo(AsrtPointsTo {
                        paren_token,
                        left,
                        dash_token,
                        gt_token,
                        right,
                    }))
                } else {
                    Ok(Self::Pure(Formula {
                        paren_token,
                        inner: left,
                    }))
                };
            }
            // Finally, we have to be in the case of a predicate call.
            // Now this one is tricky: we're parsing a call, it's starts with an expr,
            // but should absolutely avoid having a `*` at the top-level.
            let pred_call = input.parse::<AsrtPredCall>()?;

            Ok(Self::PredCall(pred_call))
        }
    }

    impl Parse for AsrtPredCall {
        fn parse(input: ParseStream) -> Result<Self> {
            let term = Term::parse_without_toplevel_star(input)?;
            match term {
                Term::MethodCall(call) => Ok(Self::MethodCall(call)),
                Term::Call(call) => Ok(Self::SimpleCall(call)),
                _ => Err(Error::new(
                    input.cursor().span(),
                    format!("Unexpected token in Assertion: {}.", input),
                )),
            }
        }
    }

    impl Parse for AsrtEmp {
        fn parse(input: ParseStream) -> Result<Self> {
            Ok(Self {
                emp_token: input.parse()?,
            })
        }
    }

    // When we're parsing expressions which occur before blocks, like in an if
    // statement's condition, we cannot parse a struct literal.
    //
    // Struct literals are ambiguous in certain positions
    // https://github.com/rust-lang/rfcs/pull/92
    pub struct AllowStruct(bool);
    pub struct AllowStar(bool);

    enum Precedence {
        Any,
        Assign,
        Impl,
        Range,
        Or,
        And,
        Compare,
        BitOr,
        BitXor,
        BitAnd,
        Shift,
        Arithmetic,
        Term,
        Cast,
    }

    impl Precedence {
        fn of(op: &BinOp) -> Self {
            match *op {
                BinOp::Add(_) | BinOp::Sub(_) => Precedence::Arithmetic,
                BinOp::Mul(_) | BinOp::Div(_) | BinOp::Rem(_) => Precedence::Term,
                BinOp::And(_) => Precedence::And,
                BinOp::Or(_) => Precedence::Or,
                BinOp::BitXor(_) => Precedence::BitXor,
                BinOp::BitAnd(_) => Precedence::BitAnd,
                BinOp::BitOr(_) => Precedence::BitOr,
                BinOp::Shl(_) | BinOp::Shr(_) => Precedence::Shift,
                BinOp::Eq(_)
                | BinOp::Lt(_)
                | BinOp::Le(_)
                | BinOp::Ne(_)
                | BinOp::Ge(_)
                | BinOp::Gt(_) => Precedence::Compare,
                BinOp::AddAssign(_)
                | BinOp::SubAssign(_)
                | BinOp::MulAssign(_)
                | BinOp::DivAssign(_)
                | BinOp::RemAssign(_)
                | BinOp::BitXorAssign(_)
                | BinOp::BitAndAssign(_)
                | BinOp::BitOrAssign(_)
                | BinOp::ShlAssign(_)
                | BinOp::ShrAssign(_) => Precedence::Assign,
                _ => todo!(),
            }
        }
    }

    impl TBlock {
        pub fn parse_within(input: ParseStream) -> Result<Vec<TermStmt>> {
            let mut stmts = Vec::new();
            loop {
                while let Some(semi) = input.parse::<Option<Token![;]>>()? {
                    stmts.push(TermStmt::Semi(Term::Verbatim(TokenStream::new()), semi));
                }
                if input.is_empty() {
                    break;
                }
                let s = parse_stmt(input, true)?;
                let requires_semicolon = if let TermStmt::Expr(s) = &s {
                    super::requires_terminator(s)
                } else {
                    false
                };
                stmts.push(s);
                if input.is_empty() {
                    break;
                } else if requires_semicolon {
                    return Err(input.error("unexpected token hello"));
                }
            }
            Ok(stmts)
        }
    }

    impl Parse for TBlock {
        fn parse(input: ParseStream) -> Result<Self> {
            let content;
            Ok(TBlock {
                brace_token: braced!(content in input),
                stmts: content.call(TBlock::parse_within)?,
            })
        }
    }

    impl Parse for TermStmt {
        fn parse(input: ParseStream) -> Result<Self> {
            parse_stmt(input, false)
        }
    }

    fn parse_stmt(input: ParseStream, allow_nosemi: bool) -> Result<TermStmt> {
        if input.peek(Token![let]) {
            stmt_local(input).map(TermStmt::Local)
        } else if input.peek(Token![use]) {
            let item: Item = input.parse()?;
            Ok(TermStmt::Item(item))
        } else {
            stmt_expr(input, allow_nosemi)
        }
    }

    fn stmt_local(input: ParseStream) -> Result<TLocal> {
        Ok(TLocal {
            let_token: input.parse()?,
            pat: {
                // let mut pat: Pat = pat::parsing::multi_pat_with_leading_vert(input)?;
                let mut pat = Pat::parse_single(input)?;
                if input.peek(Token![:]) {
                    let colon_token: Token![:] = input.parse()?;
                    let ty: Type = input.parse()?;
                    pat = Pat::Type(PatType {
                        attrs: Vec::new(),
                        pat: Box::new(pat),
                        colon_token,
                        ty: Box::new(ty),
                    });
                }
                pat
            },
            init: {
                if input.peek(Token![=]) {
                    let eq_token: Token![=] = input.parse()?;
                    let init: Term = input.parse()?;
                    Some((eq_token, Box::new(init)))
                } else {
                    None
                }
            },
            semi_token: input.parse()?,
        })
    }

    fn stmt_expr(input: ParseStream, allow_nosemi: bool) -> Result<TermStmt> {
        let e = super::parsing::term_early(input)?;

        if input.peek(Token![;]) {
            return Ok(TermStmt::Semi(e, input.parse()?));
        }

        if allow_nosemi || !super::requires_terminator(&e) {
            Ok(TermStmt::Expr(e))
        } else {
            Err(input.error("expected semicolon"))
        }
    }

    impl Parse for Term {
        fn parse(input: ParseStream) -> Result<Self> {
            ambiguous_term(input, AllowStruct(true), AllowStar(true))
        }
    }

    impl Term {
        /// An alternative to the primary `Term::parse` parser (from the
        /// [`Parse`] trait) for ambiguous syntactic positions in which a
        /// trailing brace should not be taken as part of the term.
        ///
        /// Pearlite grammar has an ambiguity where braces sometimes turn a path
        /// term into a struct initialization and sometimes do not. In the
        /// following code, the term `S {}` is one term. Presumably
        /// there is an empty struct `struct S {}` defined somewhere which it is
        /// instantiating.
        ///
        /// ```
        /// # struct S;
        /// # impl std::ops::Deref for S {
        /// #     type Target = bool;
        /// #     fn deref(&self) -> &Self::Target {
        /// #         &true
        /// #     }
        /// # }
        /// let _ = *S {};
        ///
        /// // parsed by rustc as: `*(S {})`
        /// ```
        ///
        /// We would want to parse the above using `Term::parse` after the `=`
        /// token.
        ///
        /// But in the following, `S {}` is *not* a struct init term.
        ///
        /// ```
        /// # const S: &bool = &true;
        /// if *S {} {}
        ///
        /// // parsed by rustc as:
        /// //
        /// //    if (*S) {
        /// //        /* empty block */
        /// //    }
        /// //    {
        /// //        /* another empty block */
        /// //    }
        /// ```
        ///
        /// For that reason we would want to parse if-conditions using
        /// `Term::parse_without_eager_brace` after the `if` token. Same for
        /// similar syntactic positions such as the condition expr after a
        /// `while` token or the expr at the top of a `match`.
        ///
        /// The Pearlite grammar's choices around which way this ambiguity is
        /// resolved at various syntactic positions is fairly arbitrary. Really
        /// either parse behavior could work in most positions, and language
        /// designers just decide each case based on which is more likely to be
        /// what the programmer had in mind most of the time.
        ///
        /// ```
        /// # struct S;
        /// # fn doc() -> S {
        /// if return S {} {}
        /// # unreachable!()
        /// # }
        ///
        /// // parsed by rustc as:
        /// //
        /// //    if (return (S {})) {
        /// //    }
        /// //
        /// // but could equally well have been this other arbitrary choice:
        /// //
        /// //    if (return S) {
        /// //    }
        /// //    {}
        /// ```
        ///
        /// Note the grammar ambiguity on trailing braces is distinct from
        /// precedence and is not captured by assigning a precedence level to
        /// the braced struct init expr in relation to other operators. This can
        /// be illustrated by `return 0..S {}` vs `match 0..S {}`. The former
        /// parses as `return (0..(S {}))` implying tighter precedence for
        /// struct init than `..`, while the latter parses as `match (0..S) {}`
        /// implying tighter precedence for `..` than struct init, a
        /// contradiction.
        pub fn parse_without_eager_brace(input: ParseStream) -> Result<Term> {
            ambiguous_term(input, AllowStruct(false), AllowStar(true))
        }

        pub fn parse_without_toplevel_star(input: ParseStream) -> Result<Term> {
            ambiguous_term(input, AllowStruct(true), AllowStar(false))
        }
    }

    impl Copy for AllowStruct {}

    impl Clone for AllowStruct {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl Copy for Precedence {}

    impl Clone for Precedence {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl PartialEq for Precedence {
        fn eq(&self, other: &Self) -> bool {
            *self as u8 == *other as u8
        }
    }

    impl PartialOrd for Precedence {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            let this = *self as u8;
            let other = *other as u8;
            Some(this.cmp(&other))
        }
    }

    fn parse_term(
        input: ParseStream,
        mut lhs: Term,
        allow_struct: AllowStruct,
        allow_star: AllowStar,
        base: Precedence,
    ) -> Result<Term> {
        loop {
            if Precedence::Impl >= base && input.peek(Token![==]) && input.peek3(Token![>]) {
                // a ==> b
                let eqeq_token: Token![==] = input.parse()?;
                let gt_token: Token![>] = input.parse()?;
                let precedence = Precedence::Impl;
                let mut rhs = unary_term(input, allow_struct)?;
                loop {
                    let next = peek_precedence(input);
                    if next >= precedence {
                        rhs = parse_term(input, rhs, allow_struct, AllowStar(true), next)?;
                    } else {
                        break;
                    }
                }
                lhs = Term::Impl(TermImpl {
                    hyp: Box::new(lhs),
                    eqeq_token,
                    gt_token,
                    cons: Box::new(rhs),
                });
            } else if input
                .fork()
                .parse::<BinOp>()
                .ok()
                .map_or(false, |op| Precedence::of(&op) >= base)
                && (allow_star.0 || !input.peek(Token![*]))
                && !(input.peek(Token![-]) && input.peek2(Token![>]))
            // If we find a star in the wrong context, we stop parsing
            {
                let op: BinOp = input.parse()?;
                let precedence = Precedence::of(&op);
                let mut rhs = unary_term(input, allow_struct)?;
                loop {
                    let next = peek_precedence(input);
                    if next > precedence || next == precedence && precedence == Precedence::Assign {
                        rhs = parse_term(input, rhs, allow_struct, AllowStar(true), next)?;
                    } else {
                        break;
                    }
                }
                lhs = Term::Binary(TermBinary {
                    left: Box::new(lhs),
                    op,
                    right: Box::new(rhs),
                });
            } else if Precedence::Cast >= base && input.peek(Token![as]) {
                let as_token: Token![as] = input.parse()?;
                let ty = input.call(Type::without_plus)?;
                lhs = Term::Cast(TermCast {
                    expr: Box::new(lhs),
                    as_token,
                    ty: Box::new(ty),
                });
            } else if Precedence::Cast >= base && input.peek(Token![:]) && !input.peek(Token![::]) {
                let colon_token: Token![:] = input.parse()?;
                let ty = input.call(Type::without_plus)?;
                lhs = Term::Type(TermType {
                    expr: Box::new(lhs),
                    colon_token,
                    ty: Box::new(ty),
                });
            } else {
                break;
            }
        }

        Ok(lhs)
    }

    fn peek_precedence(input: ParseStream) -> Precedence {
        if input.peek(Token![==]) && input.peek3(Token![=]) {
            Precedence::Compare
        } else if input.peek(Token![==]) && input.peek3(Token![>]) {
            Precedence::Impl
        } else if let Ok(op) = input.fork().parse() {
            Precedence::of(&op)
        } else if input.peek(Token![=]) && !input.peek(Token![=>]) {
            Precedence::Assign
        } else if input.peek(Token![..]) {
            Precedence::Range
        } else if input.peek(Token![as]) || input.peek(Token![:]) && !input.peek(Token![::]) {
            Precedence::Cast
        } else {
            Precedence::Any
        }
    }

    // Parse an arbitrary term.
    fn ambiguous_term(
        input: ParseStream,
        allow_struct: AllowStruct,
        allow_star: AllowStar,
    ) -> Result<Term> {
        let lhs = unary_term(input, allow_struct)?;
        parse_term(input, lhs, allow_struct, allow_star, Precedence::Any)
    }

    fn unary_term(input: ParseStream, allow_struct: AllowStruct) -> Result<Term> {
        if input.peek(Token![&]) {
            let and_token: Token![&] = input.parse()?;
            // TODO: Do I need raw addreses?
            // let raw: Option<raw> =
            //     if input.peek(raw) && (input.peek2(Token![mut]) || input.peek2(Token![const])) {
            //         Some(input.parse()?)
            //     } else {
            //         None
            //     };
            let mutability: Option<Token![mut]> = input.parse()?;
            // if raw.is_some() && mutability.is_none() {
            //     input.parse::<Token![const]>()?;
            // }
            let term = Box::new(unary_term(input, allow_struct)?);
            // if raw.is_some() {
            //     Ok(Expr::Verbatim(verbatim::between(begin, input)))
            // } else {
            Ok(Term::Reference(TermReference {
                and_token,
                mutability,
                term,
            }))
            // }
        } else if input.peek(Token![*]) || input.peek(Token![!]) || input.peek(Token![-]) {
            // <UnOp> <trailer>
            Ok(Term::Unary(TermUnary {
                op: input.parse()?,
                expr: Box::new(unary_term(input, allow_struct)?),
            }))
        } else {
            trailer_term(input, allow_struct)
        }
    }

    // <atom> (..<args>) ...
    // <atom> . <ident> (..<args>) ...
    // <atom> . <ident> ...
    // <atom> . <lit> ...
    // <atom> [ <expr> ] ...
    // <atom> ? ...
    fn trailer_term(input: ParseStream, allow_struct: AllowStruct) -> Result<Term> {
        let atom = atom_term(input, allow_struct)?;
        let e = trailer_helper(input, atom)?;
        Ok(e)
    }

    fn trailer_helper(input: ParseStream, mut e: Term) -> Result<Term> {
        loop {
            if input.peek(token::Paren) {
                let content;
                e = Term::Call(TermCall {
                    func: Box::new(e),
                    paren_token: parenthesized!(content in input),
                    args: content.parse_terminated(Term::parse, Token![,])?,
                });
            } else if input.peek(Token![.]) && !input.peek(Token![..]) {
                let mut dot_token: Token![.] = input.parse()?;

                let float_token: Option<LitFloat> = input.parse()?;
                if let Some(float_token) = float_token {
                    if multi_index(&mut e, &mut dot_token, float_token)? {
                        continue;
                    }
                }

                let member: Member = input.parse()?;
                let turbofish = if matches!(member, Member::Named(_)) && input.peek(Token![::]) {
                    Some(TermMethodTurbofish {
                        colon2_token: input.parse()?,
                        lt_token: input.parse()?,
                        args: {
                            let mut args = Punctuated::new();
                            loop {
                                if input.peek(Token![>]) {
                                    break;
                                }
                                let value = input.call(generic_method_argument)?;
                                args.push_value(value);
                                if input.peek(Token![>]) {
                                    break;
                                }
                                let punct = input.parse()?;
                                args.push_punct(punct);
                            }
                            args
                        },
                        gt_token: input.parse()?,
                    })
                } else {
                    None
                };

                if turbofish.is_some() || input.peek(token::Paren) {
                    if let Member::Named(method) = member {
                        let content;
                        e = Term::MethodCall(TermMethodCall {
                            receiver: Box::new(e),
                            dot_token,
                            method,
                            turbofish,
                            paren_token: parenthesized!(content in input),
                            args: content.parse_terminated(Term::parse, Token![,])?,
                        });
                        continue;
                    }
                }

                e = Term::Field(TermField {
                    base: Box::new(e),
                    dot_token,
                    member,
                });
            } else if input.peek(token::Bracket) {
                let content;
                e = Term::Index(TermIndex {
                    expr: Box::new(e),
                    bracket_token: bracketed!(content in input),
                    index: content.parse()?,
                });
            } else {
                break;
            }
        }
        Ok(e)
    }

    // Parse all atomic expressions which don't have to worry about precedence
    // interactions, as they are fully contained.
    fn atom_term(input: ParseStream, allow_struct: AllowStruct) -> Result<Term> {
        if input.peek(token::Group)
            && !input.peek2(Token![::])
            && !input.peek2(Token![!])
            && !input.peek2(token::Brace)
        {
            input.call(term_group).map(Term::Group)
        } else if input.peek(Lit) {
            input.parse().map(Term::Lit)
        } else if input.peek(Token![|]) {
            term_closure(input, allow_struct).map(Term::Closure)
        } else if input.peek(kw::forall) {
            input.parse().map(Term::Forall)
        } else if input.peek(kw::exists) {
            input.parse().map(Term::Exists)
        } else if (input.peek(Ident))
            || input.peek(Token![::])
            || input.peek(Token![<])
            || input.peek(Token![self])
            || input.peek(Token![Self])
            || input.peek(Token![super])
            || input.peek(Token![crate])
        {
            path_or_macro_or_struct(input, allow_struct)
        } else if input.peek(token::Paren) {
            paren_or_tuple(input)
        } else if input.peek(token::Bracket) {
            array_or_repeat(input)
        } else if input.peek(Token![let]) {
            input.call(term_let).map(Term::Let)
        } else if input.peek(Token![if]) {
            input.parse().map(Term::If)
        } else if input.peek(Token![match]) {
            input.parse().map(Term::Match)
        } else if input.peek(token::Brace) {
            input.call(term_block).map(Term::Block)
        } else if input.peek(Token![..]) {
            term_range(input, allow_struct).map(Term::Range)
        } else if input.peek(Lifetime) {
            let the_label: Label = input.parse()?;
            let mut expr = if input.peek(token::Brace) {
                Term::Block(input.call(term_block)?)
            } else {
                return Err(input.error("expected loop or block term"));
            };
            match &mut expr {
                Term::Block(TermBlock { label, .. }) => *label = Some(the_label),
                _ => unreachable!(),
            }
            Ok(expr)
        } else {
            Err(input.error("expected term"))
        }
    }

    fn path_or_macro_or_struct(input: ParseStream, allow_struct: AllowStruct) -> Result<Term> {
        let begin = input.fork();
        let expr: TermPath = input.parse()?;

        if expr.inner.qself.is_none() && input.peek(Token![!]) && !input.peek(Token![!=]) {
            let mut contains_arguments = false;
            for segment in &expr.inner.path.segments {
                match segment.arguments {
                    PathArguments::None => {}
                    PathArguments::AngleBracketed(_) | PathArguments::Parenthesized(_) => {
                        contains_arguments = true;
                    }
                }
            }

            if !contains_arguments {
                let _bang_token: Token![!] = input.parse()?;
                return Ok(Term::Macro(begin.parse()?));
            }
        }

        if allow_struct.0 && input.peek(token::Brace) {
            term_struct_helper(input, expr.inner.path).map(Term::Struct)
        } else {
            Ok(Term::Path(expr))
        }
    }

    fn paren_or_tuple(input: ParseStream) -> Result<Term> {
        let content;
        let paren_token = parenthesized!(content in input);
        if content.is_empty() {
            return Ok(Term::Tuple(TermTuple {
                paren_token,
                elems: Punctuated::new(),
            }));
        }

        let first: Term = content.parse()?;
        if content.is_empty() {
            return Ok(Term::Paren(TermParen {
                paren_token,
                expr: Box::new(first),
            }));
        }

        let mut elems = Punctuated::new();
        elems.push_value(first);
        while !content.is_empty() {
            let punct = content.parse()?;
            elems.push_punct(punct);
            if content.is_empty() {
                break;
            }
            let value = content.parse()?;
            elems.push_value(value);
        }
        Ok(Term::Tuple(TermTuple { paren_token, elems }))
    }

    fn array_or_repeat(input: ParseStream) -> Result<Term> {
        let content;
        let bracket_token = bracketed!(content in input);
        if content.is_empty() {
            return Ok(Term::Array(TermArray {
                bracket_token,
                elems: Punctuated::new(),
            }));
        }

        let first: Term = content.parse()?;
        if content.is_empty() || content.peek(Token![,]) {
            let mut elems = Punctuated::new();
            elems.push_value(first);
            while !content.is_empty() {
                let punct = content.parse()?;
                elems.push_punct(punct);
                if content.is_empty() {
                    break;
                }
                let value = content.parse()?;
                elems.push_value(value);
            }
            Ok(Term::Array(TermArray {
                bracket_token,
                elems,
            }))
        } else if content.peek(Token![;]) {
            let semi_token: Token![;] = content.parse()?;
            let len: Term = content.parse()?;
            Ok(Term::Repeat(TermRepeat {
                bracket_token,
                expr: Box::new(first),
                semi_token,
                len: Box::new(len),
            }))
        } else {
            Err(content.error("expected `,` or `;`"))
        }
    }

    pub(crate) fn term_early(input: ParseStream) -> Result<Term> {
        let mut expr = if input.peek(Token![if]) {
            Term::If(input.parse()?)
        } else if input.peek(Token![match]) {
            Term::Match(input.parse()?)
        } else if input.peek(token::Brace) {
            Term::Block(input.call(term_block)?)
        } else {
            let allow_struct = AllowStruct(true);
            let allow_star = AllowStar(true);
            let expr = unary_term(input, allow_struct)?;

            return parse_term(input, expr, allow_struct, allow_star, Precedence::Any);
        };

        if input.peek(Token![.]) && !input.peek(Token![..]) || input.peek(Token![?]) {
            expr = trailer_helper(input, expr)?;

            let allow_struct = AllowStruct(true);
            let allow_star = AllowStar(true);
            return parse_term(input, expr, allow_struct, allow_star, Precedence::Any);
        }

        Ok(expr)
    }

    impl Parse for TermLit {
        fn parse(input: ParseStream) -> Result<Self> {
            Ok(TermLit {
                lit: input.parse()?,
            })
        }
    }

    fn term_group<'a>(input: ParseStream) -> Result<TermGroup> {
        unimplemented!("GROUP")
        // input
        //     .parse_any_delimiter()
        //     .and_then(|(delim, span, content)| {
        //         assert_eq!(delim, Delimiter::None);
        //         Ok(TermGroup {
        //             group_token: token::Group(span.join()),
        //             expr: content.parse()?,
        //         })
        //     })
    }

    fn generic_method_argument(input: ParseStream) -> Result<TermGenericMethodArgument> {
        if input.peek(Lit) {
            let lit = input.parse()?;
            return Ok(TermGenericMethodArgument::Const(Term::Lit(lit)));
        }

        if input.peek(token::Brace) {
            let block = input.call(super::parsing::term_block)?;
            return Ok(TermGenericMethodArgument::Const(Term::Block(block)));
        }

        input.parse().map(TermGenericMethodArgument::Type)
    }

    fn term_let(input: ParseStream) -> Result<TermLet> {
        Ok(TermLet {
            let_token: input.parse()?,
            pat: Pat::parse_single(input)?,
            // pat: pat::parsing::multi_pat_with_leading_vert(input)?,
            eq_token: input.parse()?,
            expr: Box::new(input.call(Term::parse_without_eager_brace)?),
        })
    }

    impl Parse for TermIf {
        fn parse(input: ParseStream) -> Result<Self> {
            Ok(TermIf {
                if_token: input.parse()?,
                cond: Box::new(input.call(Term::parse_without_eager_brace)?),
                then_branch: input.parse()?,
                else_branch: {
                    if input.peek(Token![else]) {
                        Some(input.call(else_block)?)
                    } else {
                        None
                    }
                },
            })
        }
    }

    fn else_block(input: ParseStream) -> Result<(Token![else], Box<Term>)> {
        let else_token: Token![else] = input.parse()?;

        let lookahead = input.lookahead1();
        let else_branch = if input.peek(Token![if]) {
            input.parse().map(Term::If)?
        } else if input.peek(token::Brace) {
            Term::Block(TermBlock {
                label: None,
                block: input.parse()?,
            })
        } else {
            return Err(lookahead.error());
        };

        Ok((else_token, Box::new(else_branch)))
    }

    impl Parse for TermMatch {
        fn parse(input: ParseStream) -> Result<Self> {
            let match_token: Token![match] = input.parse()?;
            let expr = Term::parse_without_eager_brace(input)?;

            let content;
            let brace_token = braced!(content in input);

            let mut arms = Vec::new();
            while !content.is_empty() {
                arms.push(content.call(TermArm::parse)?);
            }

            Ok(TermMatch {
                match_token,
                expr: Box::new(expr),
                brace_token,
                arms,
            })
        }
    }

    impl Parse for TermForall {
        fn parse(input: ParseStream) -> Result<Self> {
            let forall_token = input.parse()?;
            let lt_token: Token![<] = input.parse()?;

            let mut args = Punctuated::new();
            while !input.peek(Token![>]) {
                let quantarg = input.parse()?;
                args.push_value(quantarg);
                if input.peek(Token![>]) {
                    break;
                }

                let punct = input.parse()?;
                args.push_punct(punct);
            }

            let gt_token: Token![>] = input.parse()?;

            let term = input.parse()?;

            Ok(TermForall {
                forall_token,
                lt_token,
                args,
                gt_token,
                term,
            })
        }
    }

    impl Parse for TermExists {
        fn parse(input: ParseStream) -> Result<Self> {
            let exists_token = input.parse()?;
            let lt_token: Token![<] = input.parse()?;

            let mut args = Punctuated::new();
            while !input.peek(Token![>]) {
                let quantarg = input.parse()?;
                args.push_value(quantarg);
                if input.peek(Token![>]) {
                    break;
                }

                let punct = input.parse()?;
                args.push_punct(punct);
            }

            let gt_token: Token![>] = input.parse()?;

            let term = input.parse()?;

            Ok(TermExists {
                exists_token,
                lt_token,
                args,
                gt_token,
                term,
            })
        }
    }
    impl Parse for QuantArg {
        fn parse(input: ParseStream) -> Result<Self> {
            let ident = input.parse()?;
            let colon_token = input.parse()?;
            let ty = input.parse()?;
            Ok(QuantArg {
                ident,
                colon_token,
                ty,
            })
        }
    }

    macro_rules! impl_by_parsing_term {
        (
            $(
                $term_type:ty, $variant:ident, $msg:expr,
            )*
        ) => {
            $(
                impl Parse for $term_type {
                    fn parse(input: ParseStream) -> Result<Self> {
                        let mut expr: Term = input.parse()?;
                        loop {
                            match expr {
                                Term::$variant(inner) => return Ok(inner),
                                Term::Group(next) => expr = *next.expr,
                                _ => return Err(Error::new_spanned(expr, $msg)),
                            }
                        }
                    }
                }
            )*
        };
    }

    impl_by_parsing_term! {
        TermArray, Array, "expected slice literal term",
        TermCall, Call, "expected function call term",
        TermMethodCall, MethodCall, "expected method call term",
        TermTuple, Tuple, "expected tuple term",
        TermBinary, Binary, "expected binary operation",
        TermUnary, Unary, "expected unary operation",
        TermCast, Cast, "expected cast term",
        TermType, Type, "expected type ascription term",
        TermLet, Let, "expected let guard",
        TermField, Field, "expected struct field access",
        TermIndex, Index, "expected indexing term",
        TermRange, Range, "expected range term",
        TermStruct, Struct, "expected struct literal term",
        TermRepeat, Repeat, "expected array literal constructed from one repeated element",
        TermParen, Paren, "expected parenthesized term",
    }

    impl Parse for TermFieldValue {
        fn parse(input: ParseStream) -> Result<Self> {
            let member: Member = input.parse()?;
            let (colon_token, value) =
                if input.peek(Token![:]) || !matches!(member, Member::Named(_)) {
                    let colon_token: Token![:] = input.parse()?;
                    let value: Term = input.parse()?;
                    (Some(colon_token), value)
                } else if let Member::Named(ident) = &member {
                    let value = Term::Path(TermPath {
                        inner: ExprPath {
                            qself: None,
                            path: Path::from(ident.clone()),
                            attrs: Vec::new(),
                        },
                    });
                    (None, value)
                } else {
                    unreachable!()
                };

            Ok(TermFieldValue {
                member,
                colon_token,
                expr: value,
            })
        }
    }

    fn term_struct_helper(input: ParseStream, path: Path) -> Result<TermStruct> {
        let content;
        let brace_token = braced!(content in input);

        let mut fields = Punctuated::new();
        while !content.is_empty() {
            if content.peek(Token![..]) {
                return Ok(TermStruct {
                    brace_token,
                    path,
                    fields,
                    dot2_token: Some(content.parse()?),
                    rest: Some(Box::new(content.parse()?)),
                });
            }

            fields.push(content.parse()?);
            if content.is_empty() {
                break;
            }
            let punct: Token![,] = content.parse()?;
            fields.push_punct(punct);
        }

        Ok(TermStruct {
            brace_token,
            path,
            fields,
            dot2_token: None,
            rest: None,
        })
    }

    pub fn term_block(input: ParseStream) -> Result<TermBlock> {
        let label: Option<Label> = input.parse()?;

        let content;
        let brace_token = braced!(content in input);
        let stmts = content.call(TBlock::parse_within)?;

        Ok(TermBlock {
            label,
            block: TBlock { brace_token, stmts },
        })
    }

    fn term_range(input: ParseStream, allow_struct: AllowStruct) -> Result<TermRange> {
        Ok(TermRange {
            from: None,
            limits: input.parse()?,
            to: {
                if input.is_empty()
                    || input.peek(Token![,])
                    || input.peek(Token![;])
                    || !allow_struct.0 && input.peek(token::Brace)
                {
                    None
                } else {
                    let to = ambiguous_term(input, allow_struct, AllowStar(true))?;
                    Some(Box::new(to))
                }
            },
        })
    }

    impl Parse for TermPath {
        fn parse(input: ParseStream) -> Result<Self> {
            let exp_path: ExprPath = input.parse()?;

            // let (qself, path) = syn::path::parsing::qpath(input, true)?;
            // Ok(TermPath { qself: exp_path.qself, path: exp_path.path })
            Ok(TermPath { inner: exp_path })
        }
    }

    impl Parse for TermArm {
        fn parse(input: ParseStream) -> Result<TermArm> {
            let requires_comma;
            Ok(TermArm {
                // pat: todo!("Arm"),
                pat: Pat::parse_multi(input)?,
                // pat: pat::parsing::multi_pat_with_leading_vert(input)?,
                guard: {
                    if input.peek(Token![if]) {
                        let if_token: Token![if] = input.parse()?;
                        let guard: Term = input.parse()?;
                        Some((if_token, Box::new(guard)))
                    } else {
                        None
                    }
                },
                fat_arrow_token: input.parse()?,
                body: {
                    let body = input.call(term_early)?;
                    requires_comma = requires_terminator(&body);
                    Box::new(body)
                },
                comma: {
                    if requires_comma && !input.is_empty() {
                        Some(input.parse()?)
                    } else {
                        input.parse()?
                    }
                },
            })
        }
    }

    impl Parse for super::Index {
        fn parse(input: ParseStream) -> Result<Self> {
            let lit: LitInt = input.parse()?;
            if lit.suffix().is_empty() {
                Ok(super::Index {
                    index: lit
                        .base10_digits()
                        .parse()
                        .map_err(|err| Error::new(lit.span(), err))?,
                    span: lit.span(),
                })
            } else {
                Err(Error::new(lit.span(), "expected unsuffixed integer"))
            }
        }
    }

    fn multi_index(e: &mut Term, dot_token: &mut Token![.], float: LitFloat) -> Result<bool> {
        let mut float_repr = float.to_string();
        let trailing_dot = float_repr.ends_with('.');
        if trailing_dot {
            float_repr.truncate(float_repr.len() - 1);
        }
        for part in float_repr.split('.') {
            let index = syn::parse_str(part).map_err(|err| Error::new(float.span(), err))?;
            let base = mem::replace(e, Term::__Nonexhaustive);
            *e = Term::Field(TermField {
                base: Box::new(base),
                dot_token: Token![.](dot_token.span),
                member: Member::Unnamed(index),
            });
            *dot_token = Token![.](float.span());
        }
        Ok(!trailing_dot)
    }

    fn term_closure(input: ParseStream, allow_struct: AllowStruct) -> Result<TermClosure> {
        let or1_token: Token![|] = input.parse()?;

        let mut inputs = Punctuated::new();
        loop {
            if input.peek(Token![|]) {
                break;
            }
            let value = closure_arg(input)?;
            inputs.push_value(value);
            if input.peek(Token![|]) {
                break;
            }
            let punct: Token![,] = input.parse()?;
            inputs.push_punct(punct);
        }

        let or2_token: Token![|] = input.parse()?;

        let (output, body) = if input.peek(Token![->]) {
            let arrow_token: Token![->] = input.parse()?;
            let ty: Type = input.parse()?;
            let body: TBlock = input.parse()?;
            let output = ReturnType::Type(arrow_token, Box::new(ty));
            let block = Term::Block(TermBlock {
                label: None,
                block: body,
            });
            (output, block)
        } else {
            let body = ambiguous_term(input, allow_struct, AllowStar(true))?;
            (ReturnType::Default, body)
        };

        Ok(TermClosure {
            attrs: Vec::new(),
            or1_token,
            inputs,
            or2_token,
            output,
            body: Box::new(body),
        })
    }

    fn closure_arg(input: ParseStream) -> Result<Pat> {
        let attrs = input.call(Attribute::parse_outer)?;
        let mut pat = Pat::parse_single(input)?;

        if input.peek(Token![:]) {
            Ok(Pat::Type(PatType {
                attrs,
                pat: Box::new(pat),
                colon_token: input.parse()?,
                ty: input.parse()?,
            }))
        } else {
            match &mut pat {
                Pat::Ident(pat) => pat.attrs = attrs,
                Pat::Lit(pat) => pat.attrs = attrs,
                Pat::Macro(pat) => pat.attrs = attrs,
                Pat::Or(pat) => pat.attrs = attrs,
                Pat::Path(pat) => pat.attrs = attrs,
                Pat::Range(pat) => pat.attrs = attrs,
                Pat::Reference(pat) => pat.attrs = attrs,
                Pat::Rest(pat) => pat.attrs = attrs,
                Pat::Slice(pat) => pat.attrs = attrs,
                Pat::Struct(pat) => pat.attrs = attrs,
                Pat::Tuple(pat) => pat.attrs = attrs,
                Pat::TupleStruct(pat) => pat.attrs = attrs,
                Pat::Type(_) => unreachable!(),
                Pat::Verbatim(_) => {}
                Pat::Wild(pat) => pat.attrs = attrs,
                _ => unreachable!(),
            }
            Ok(pat)
        }
    }
}

pub(crate) mod printing {
    use super::*;
    use crate::print::TokensOrDefault;
    use proc_macro2::{Literal, TokenStream};
    use quote::{ToTokens, TokenStreamExt};

    // If the given term is a bare `TermStruct`, wraps it in parenthesis
    // before appending it to `TokenStream`.
    fn wrap_bare_struct(tokens: &mut TokenStream, e: &Term) {
        if let Term::Struct(_) = *e {
            token::Paren::default().surround(tokens, |tokens| {
                e.to_tokens(tokens);
            });
        } else {
            e.to_tokens(tokens);
        }
    }

    impl ToTokens for Assertion {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.pipe1.to_tokens(tokens);
            self.lvars.to_tokens(tokens);
            self.pipe2.to_tokens(tokens);
            self.def.to_tokens(tokens);
        }
    }

    impl ToTokens for LvarDecl {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.ident.to_tokens(tokens);
            if let Some((colon, ty)) = &self.ty_opt {
                colon.to_tokens(tokens);
                ty.to_tokens(tokens);
            }
        }
    }

    impl ToTokens for AsrtEmp {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.emp_token.to_tokens(tokens)
        }
    }

    impl ToTokens for AsrtPointsTo {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.paren_token.surround(tokens, |tokens| {
                self.left.to_tokens(tokens);
                self.dash_token.to_tokens(tokens);
                self.gt_token.to_tokens(tokens);
                self.right.to_tokens(tokens)
            })
        }
    }

    impl ToTokens for AsrtPredCall {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                Self::MethodCall(mth) => mth.to_tokens(tokens),
                Self::SimpleCall(mth) => mth.to_tokens(tokens),
            }
        }
    }

    impl ToTokens for Formula {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.paren_token
                .surround(tokens, |tokens| self.inner.to_tokens(tokens))
        }
    }

    impl ToTokens for Observation {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.open_dollar.to_tokens(tokens);
            self.inner.to_tokens(tokens);
            self.close_dollar.to_tokens(tokens);
        }
    }

    impl ToTokens for QuantArg {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.ident.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
        }
    }

    impl ToTokens for TermForall {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.forall_token.to_tokens(tokens);
            self.lt_token.to_tokens(tokens);
            self.args.to_tokens(tokens);
            self.gt_token.to_tokens(tokens);
            self.term.to_tokens(tokens);
        }
    }

    impl ToTokens for TermExists {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.exists_token.to_tokens(tokens);
            self.lt_token.to_tokens(tokens);
            self.args.to_tokens(tokens);
            self.gt_token.to_tokens(tokens);
            self.term.to_tokens(tokens);
        }
    }

    impl ToTokens for TermImpl {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.hyp.to_tokens(tokens);
            self.eqeq_token.to_tokens(tokens);
            self.gt_token.to_tokens(tokens);
            self.cons.to_tokens(tokens);
        }
    }

    impl ToTokens for TBlock {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.brace_token.surround(tokens, |tokens| {
                tokens.append_all(&self.stmts);
            });
        }
    }

    impl ToTokens for TermStmt {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                TermStmt::Local(local) => local.to_tokens(tokens),
                TermStmt::Expr(expr) => expr.to_tokens(tokens),
                TermStmt::Semi(expr, semi) => {
                    expr.to_tokens(tokens);
                    semi.to_tokens(tokens);
                }
                TermStmt::Item(i) => i.to_tokens(tokens),
            }
        }
    }

    impl ToTokens for TLocal {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.let_token.to_tokens(tokens);
            self.pat.to_tokens(tokens);
            if let Some((eq_token, init)) = &self.init {
                eq_token.to_tokens(tokens);
                init.to_tokens(tokens);
            }
            self.semi_token.to_tokens(tokens);
        }
    }

    impl ToTokens for TermArray {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.bracket_token.surround(tokens, |tokens| {
                self.elems.to_tokens(tokens);
            })
        }
    }

    impl ToTokens for TermCall {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.func.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.args.to_tokens(tokens);
            })
        }
    }

    impl ToTokens for TermMethodCall {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.receiver.to_tokens(tokens);
            self.dot_token.to_tokens(tokens);
            self.method.to_tokens(tokens);
            self.turbofish.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.args.to_tokens(tokens);
            });
        }
    }

    impl ToTokens for TermClosure {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(&self.attrs);
            self.or1_token.to_tokens(tokens);
            self.inputs.to_tokens(tokens);
            self.or2_token.to_tokens(tokens);
            self.output.to_tokens(tokens);
            self.body.to_tokens(tokens);
        }
    }

    impl ToTokens for TermMethodTurbofish {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.colon2_token.to_tokens(tokens);
            self.lt_token.to_tokens(tokens);
            self.args.to_tokens(tokens);
            self.gt_token.to_tokens(tokens);
        }
    }

    impl ToTokens for TermGenericMethodArgument {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                TermGenericMethodArgument::Type(t) => t.to_tokens(tokens),
                TermGenericMethodArgument::Const(c) => c.to_tokens(tokens),
            }
        }
    }

    impl ToTokens for TermTuple {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.paren_token.surround(tokens, |tokens| {
                self.elems.to_tokens(tokens);
                // If we only have one argument, we need a trailing comma to
                // distinguish TermTuple from TermParen.
                if self.elems.len() == 1 && !self.elems.trailing_punct() {
                    <Token![,]>::default().to_tokens(tokens);
                }
            })
        }
    }

    impl ToTokens for TermBinary {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.left.to_tokens(tokens);
            self.op.to_tokens(tokens);
            self.right.to_tokens(tokens);
        }
    }

    impl ToTokens for TermUnary {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.op.to_tokens(tokens);
            self.expr.to_tokens(tokens);
        }
    }

    impl ToTokens for TermLit {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.lit.to_tokens(tokens);
        }
    }

    impl ToTokens for TermCast {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.expr.to_tokens(tokens);
            self.as_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
        }
    }

    impl ToTokens for TermType {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.expr.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
        }
    }

    // impl ToTokens for TermLogVar {
    //     fn to_tokens(&self, tokens: &mut TokenStream) {
    //         self.hash_token.to_tokens(tokens);
    //         self.ident.to_tokens(tokens);
    //     }
    // }

    fn maybe_wrap_else(tokens: &mut TokenStream, else_: &Option<(Token![else], Box<Term>)>) {
        if let Some((else_token, else_)) = else_ {
            else_token.to_tokens(tokens);

            // If we are not one of the valid expressions to exist in an else
            // clause, wrap ourselves in a block.
            match **else_ {
                Term::If(_) | Term::Block(_) => {
                    else_.to_tokens(tokens);
                }
                _ => {
                    token::Brace::default().surround(tokens, |tokens| {
                        else_.to_tokens(tokens);
                    });
                }
            }
        }
    }

    impl ToTokens for TermLet {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.let_token.to_tokens(tokens);
            self.pat.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            wrap_bare_struct(tokens, &self.expr);
        }
    }

    impl ToTokens for TermIf {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.if_token.to_tokens(tokens);
            wrap_bare_struct(tokens, &self.cond);
            self.then_branch.to_tokens(tokens);
            maybe_wrap_else(tokens, &self.else_branch);
        }
    }

    impl ToTokens for TermMatch {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.match_token.to_tokens(tokens);
            wrap_bare_struct(tokens, &self.expr);
            self.brace_token.surround(tokens, |tokens| {
                for (i, arm) in self.arms.iter().enumerate() {
                    arm.to_tokens(tokens);
                    // Ensure that we have a comma after a non-block arm, except
                    // for the last one.
                    let is_last = i == self.arms.len() - 1;
                    if !is_last && requires_terminator(&arm.body) && arm.comma.is_none() {
                        <Token![,]>::default().to_tokens(tokens);
                    }
                }
            });
        }
    }

    impl ToTokens for TermBlock {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.label.to_tokens(tokens);
            self.block.brace_token.surround(tokens, |tokens| {
                tokens.append_all(&self.block.stmts);
            });
        }
    }

    impl ToTokens for TermField {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.base.to_tokens(tokens);
            self.dot_token.to_tokens(tokens);
            self.member.to_tokens(tokens);
        }
    }

    // TODO: Figure out why rust thinks this is form syn
    impl ToTokens for super::Index {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let mut lit = Literal::i64_unsuffixed(i64::from(self.index));
            lit.set_span(self.span);
            tokens.append(lit);
        }
    }

    impl ToTokens for TermIndex {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.expr.to_tokens(tokens);
            self.bracket_token.surround(tokens, |tokens| {
                self.index.to_tokens(tokens);
            });
        }
    }

    impl ToTokens for TermRange {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.from.to_tokens(tokens);
            match &self.limits {
                RangeLimits::HalfOpen(t) => t.to_tokens(tokens),
                RangeLimits::Closed(t) => t.to_tokens(tokens),
            }
            self.to.to_tokens(tokens);
        }
    }

    impl ToTokens for TermPath {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.inner.to_tokens(tokens)
            // private::print_path(tokens, &self.qself, &self.path);
        }
    }

    impl ToTokens for TermStruct {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.path.to_tokens(tokens);
            self.brace_token.surround(tokens, |tokens| {
                self.fields.to_tokens(tokens);
                if self.rest.is_some() {
                    TokensOrDefault(&self.dot2_token).to_tokens(tokens);
                    self.rest.to_tokens(tokens);
                }
            })
        }
    }

    impl ToTokens for TermRepeat {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.bracket_token.surround(tokens, |tokens| {
                self.expr.to_tokens(tokens);
                self.semi_token.to_tokens(tokens);
                self.len.to_tokens(tokens);
            })
        }
    }

    impl ToTokens for TermReference {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.and_token.to_tokens(tokens);
            self.mutability.to_tokens(tokens);
            self.term.to_tokens(tokens);
        }
    }

    impl ToTokens for TermGroup {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.group_token.surround(tokens, |tokens| {
                self.expr.to_tokens(tokens);
            });
        }
    }

    impl ToTokens for TermParen {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.paren_token.surround(tokens, |tokens| {
                self.expr.to_tokens(tokens);
            });
        }
    }

    impl ToTokens for TermFieldValue {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.member.to_tokens(tokens);
            if let Some(colon_token) = &self.colon_token {
                colon_token.to_tokens(tokens);
                self.expr.to_tokens(tokens);
            }
        }
    }

    impl ToTokens for TermArm {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.pat.to_tokens(tokens);
            if let Some((if_token, guard)) = &self.guard {
                if_token.to_tokens(tokens);
                guard.to_tokens(tokens);
            }
            self.fat_arrow_token.to_tokens(tokens);
            self.body.to_tokens(tokens);
            self.comma.to_tokens(tokens);
        }
    }
}
