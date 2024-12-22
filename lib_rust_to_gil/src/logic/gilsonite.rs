use itertools::Itertools;
use num_bigint::BigInt;
use rustc_ast::{LitKind, Mutability};
use rustc_hir::def_id::DefId;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::{self, interpret::Scalar, BorrowKind, ConstValue, UnOp},
    query::Key,
    thir::{self, AdtExpr, BlockId, ClosureExpr, ExprId, LogicalOp, Pat, StmtId, Thir},
    ty::{self, GenericArgs, GenericArgsRef, Ty, TyCtxt, TyKind, UpvarArgs},
};

use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::{sym::panic_misaligned_pointer_dereference, Symbol};
use rustc_target::abi::{FieldIdx, VariantIdx};

use crate::{
    logic::predicate::fn_args_and_tys,
    signature::{anonymous_param_symbol, inputs_and_output},
};

use super::{builtins::LogicStubs, fatal2};

#[derive(Debug, Clone)]
pub struct EncDeBigInt(pub BigInt);

impl<I: Into<BigInt>> From<I> for EncDeBigInt {
    fn from(i: I) -> Self {
        EncDeBigInt(i.into())
    }
}

const BIGINT_SENTINEL: u8 = 0;

impl<S: Encoder> Encodable<S> for EncDeBigInt {
    fn encode(&self, s: &mut S) {
        let bytes = self.0.to_signed_bytes_le();
        s.emit_usize(bytes.len());
        s.emit_raw_bytes(bytes.as_slice());
        // The last element of an array of bytes in little-endian form
        // cannot be 0. So we add a 0 to check for syn, as done with STR_SENTIEL
        // in the rustc implementation for strings.
        s.emit_u8(BIGINT_SENTINEL);
    }
}

impl<D: Decoder> Decodable<D> for EncDeBigInt {
    fn decode(d: &mut D) -> Self {
        let len = d.read_usize();
        let bytes = d.read_raw_bytes(len + 1);
        assert!(bytes[len] == BIGINT_SENTINEL);
        let bigint = BigInt::from_signed_bytes_le(&bytes[..len]);
        EncDeBigInt(bigint)
    }
}

/// Pure logical terms, must have no spatial or resource component.
#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum ExprKind<'tcx> {
    Call {
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
        args: Vec<Expr<'tcx>>,
    },
    BinOp {
        left: Box<Expr<'tcx>>,
        op: BinOp,
        right: Box<Expr<'tcx>>,
    },
    UnOp {
        op: UnOp,
        arg: Box<Expr<'tcx>>,
    },
    Constructor {
        def_id: DefId,
        _args: GenericArgsRef<'tcx>,
        fields: Vec<Expr<'tcx>>,
        variant_index: VariantIdx,
    },
    Tuple {
        fields: Vec<Expr<'tcx>>,
    },
    Field {
        lhs: Box<Expr<'tcx>>,
        field: FieldIdx,
    },
    Var {
        id: Symbol,
    },
    Integer {
        #[type_foldable(identity)]
        #[type_visitable(ignore)]
        value: EncDeBigInt,
    },
    True,
    False,
    // Unclear whether this is worth distinguishing in the AST or just delegating this to the backend
    SeqNil,
    SeqOp {
        op: SeqOp,
        args: Vec<Expr<'tcx>>,
    },
    ZST,
    SetProphecy {
        mut_ref: Box<Expr<'tcx>>,
        prophecy: Box<Expr<'tcx>>,
    },
    GetProphecy {
        mut_ref: Box<Expr<'tcx>>,
    },
    GetValue {
        mut_ref: Box<Expr<'tcx>>,
    },
    Exists {
        var: (Symbol, Ty<'tcx>),
        body: Box<Expr<'tcx>>,
    },
    EForall {
        var: (Symbol, Ty<'tcx>),
        body: Box<Expr<'tcx>>,
    },
    PtrToMutRef {
        ptr: Box<Expr<'tcx>>,
    },
}

impl<'tcx> ExprKind<'tcx> {
    fn mk_exists(var: (Symbol, Ty<'tcx>), body: Box<Expr<'tcx>>) -> Self {
        Self::Exists { var, body }
    }

    fn mk_forall(var: (Symbol, Ty<'tcx>), body: Box<Expr<'tcx>>) -> Self {
        Self::EForall { var, body }
    }
}

#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum FormulaKind<'tcx> {
    // True,
    // False,
    FOp {
        left: Box<FormulaKind<'tcx>>,
        op: FOp,
        right: Box<FormulaKind<'tcx>>,
    },
    EOp {
        left: Box<Expr<'tcx>>,
        op: EOp,
        right: Box<Expr<'tcx>>,
    },
    Neg {
        form: Box<FormulaKind<'tcx>>,
    },
}

/// Propositional operators
#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum FOp {
    Impl,
    Or,
    And,
}

/// Expression operations
#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
#[allow(dead_code)]
pub enum EOp {
    Lt,
    Le,
    Eq,
    Ne,
    SetMem,
    SetSub,
}

#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum SeqOp {
    Append,
    Prepend,
    Concat,
    Head,
    Last,
    Tail,
    Len,
    At,
    Sub,
    Repeat,
}

#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
#[allow(dead_code)]
pub enum BinOp {
    Eq,
    Lt,
    Le,
    Ne,
    Sub,
    Add,
    Div,
    Mul,
    Rem,
    Shl,
    And,
    Or,
    Impl,
    Ge,
    Gt,
}

#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct Formula<'tcx> {
    pub bound_vars: Vec<(Symbol, Ty<'tcx>)>,
    pub body: FormulaKind<'tcx>,
}

#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct Expr<'tcx> {
    pub kind: ExprKind<'tcx>,
    pub ty: Ty<'tcx>,
}

#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct Assert<'tcx> {
    pub kind: AssertKind<'tcx>,
}

#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct Predicate<'tcx> {
    pub disjuncts: Vec<(Vec<(Symbol, Ty<'tcx>)>, Assert<'tcx>)>,
}

#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct AssertPredCall<'tcx> {
    pub def_id: DefId,
    pub substs: GenericArgsRef<'tcx>,
    pub args: Vec<Expr<'tcx>>,
}

#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum AssertKind<'tcx> {
    /// Separating conjunction
    Star {
        left: Box<Assert<'tcx>>,
        right: Box<Assert<'tcx>>,
    },
    /// Pure expressions: includes constructors for types, pure logic functions etc...
    Formula {
        formula: Formula<'tcx>,
    },
    /// Predicate calls
    Call(AssertPredCall<'tcx>),
    /// Rust Points to predicate
    PointsTo {
        // TODO(xavier): Should probably be a Place, but that requires building the places first.
        src: Expr<'tcx>,
        tgt: Expr<'tcx>,
    },
    Emp,
    Observation {
        expr: Expr<'tcx>,
    },
    ProphecyController {
        prophecy: Expr<'tcx>,
        model: Expr<'tcx>,
    },
    ProphecyObserver {
        prophecy: Expr<'tcx>,
        model: Expr<'tcx>,
    },
    PointsToSlice {
        src: Expr<'tcx>,
        size: Expr<'tcx>,
        pointees: Expr<'tcx>,
    },
    Uninit {
        pointer: Expr<'tcx>,
    },
    ManyUninits {
        pointer: Expr<'tcx>,
        size: Expr<'tcx>,
    },
    MaybeUninit {
        pointer: Expr<'tcx>,
        pointee: Expr<'tcx>,
    },
    ManyMaybeUninits {
        pointer: Expr<'tcx>,
        pointees: Expr<'tcx>,
        size: Expr<'tcx>,
    },
    Wand {
        lhs: Box<Assert<'tcx>>,
        rhs: Box<Assert<'tcx>>,
    },
    Let {
        pattern: Pattern<'tcx>,
        arg: Expr<'tcx>,
        body: Box<Assert<'tcx>>,
    },
    // ... other core predicates
}

#[derive(Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
pub enum Pattern<'tcx> {
    Constructor {
        adt: DefId,
        substs: GenericArgsRef<'tcx>,
        variant: VariantIdx,
        fields: Vec<Pattern<'tcx>>,
    },
    Tuple(Vec<Pattern<'tcx>>),
    Wildcard(Ty<'tcx>),
    Binder(Symbol),
    Boolean(bool),
}

#[derive(Debug)]
pub enum ProofStep<'tcx> {
    Package {
        pre: AssertPredCall<'tcx>,
        post: AssertPredCall<'tcx>,
    },
    Unfold {
        pred: AssertPredCall<'tcx>,
    },
    Fold {
        pred: AssertPredCall<'tcx>,
    },
    If {
        cond: Expr<'tcx>,
        t_branch: Vec<ProofStep<'tcx>>,
        f_branch: Vec<ProofStep<'tcx>>,
    },
    Call {
        lemma_call: AssertPredCall<'tcx>,
    },
    AssertBind {
        vars: Vec<Symbol>,
        assertion: Assert<'tcx>,
    },
    Assume {
        formula: Formula<'tcx>,
    },
}

#[derive(Debug, Clone, TyDecodable, TyEncodable)]
pub struct SpecTerm<'tcx> {
    pub uni: Vec<(Symbol, Ty<'tcx>)>,
    pub pre: Assert<'tcx>,
    pub posts: Vec<(Vec<(Symbol, Ty<'tcx>)>, Assert<'tcx>)>,
    pub trusted: bool,
}

#[derive(Debug)]
pub struct ExtractLemmaTerm<'tcx> {
    pub uni: Vec<(Symbol, Ty<'tcx>)>,
    pub models: Option<((Symbol, Ty<'tcx>), (Symbol, Ty<'tcx>))>,
    pub assuming: Formula<'tcx>,
    pub from: AssertPredCall<'tcx>,
    pub extract: AssertPredCall<'tcx>,
    pub proph_model: Option<((Symbol, Ty<'tcx>), (Symbol, Ty<'tcx>))>,
    pub prophecise: Expr<'tcx>,
}

impl<'tcx> Assert<'tcx> {
    pub fn unstar(&self) -> Vec<&Self> {
        let mut r = Vec::new();

        self.unstar_inner(&mut r);

        r
    }
    fn unstar_inner<'a>(&'a self, pars: &mut Vec<&'a Self>) {
        match &self.kind {
            AssertKind::Star { left, right } => {
                left.unstar_inner(pars);
                right.unstar_inner(pars);
            }
            _ => pars.push(self),
        }
    }

    pub fn star(self, other: Assert<'tcx>) -> Self {
        match (&self.kind, &other.kind) {
            (AssertKind::Emp, _) => other,
            (_, AssertKind::Emp) => self,
            _ => Assert {
                kind: AssertKind::Star {
                    left: Box::new(self),
                    right: Box::new(other),
                },
            },
        }
    }
}

impl<'tcx> FromIterator<Assert<'tcx>> for Assert<'tcx> {
    fn from_iter<T: IntoIterator<Item = Assert<'tcx>>>(iter: T) -> Self {
        iter.into_iter().fold(
            Assert {
                kind: AssertKind::Emp,
            },
            |acc, a| acc.star(a),
        )
    }
}

pub struct GilsoniteBuilder<'tcx> {
    thir: Thir<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> GilsoniteBuilder<'tcx> {
    pub fn new(thir: Thir<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self { thir, tcx }
    }

    pub(crate) fn build_extract_lemma(&self, expr: ExprId) -> ExtractLemmaTerm<'tcx> {
        let (uni, (assuming, from, extract, proph_model, prophecise)) =
            self.peel_lvar_bindings(expr, |this, expr| {
                this.peel_lvar_bindings(expr, |this, expr| {
                    let expr = this.peel_scope(expr);
                    let thir::ExprKind::Call {
                        ty, fun: _, args, ..
                    } = &this.thir[expr].kind
                    else {
                        unreachable!("ill formed extract lemma block {:?}", this.thir[expr])
                    };

                    let Some(LogicStubs::ExtractLemma) = this.get_stub(*ty) else {
                        unreachable!("ill formed extract lemma block")
                    };

                    let assuming = this.build_formula(args[0]);
                    let AssertKind::Call(from) = this.build_assert_kind(args[1]) else {
                        unreachable!(
                        "ill formed extract lemma block, second argument must be a predicate call"
                    )
                    };
                    let AssertKind::Call(extract) = this.build_assert_kind(args[2]) else {
                        unreachable!(
                        "ill formed extract lemma block, third argument must be a predicate call"
                    )
                    };

                    // In no-proph mode, this will always be unit, but it's easier than to construct it.
                    let mut prophecise = this.peel_lvar_bindings(args[3], |this, expr| {
                        let expr = this.peel_scope(expr);
                        this.build_expression(expr)
                    });
                    assert!(prophecise.0.len() == 0 || prophecise.0.len() == 2);
                    let proph_model = if prophecise.0.len() == 2 {
                        Some((prophecise.0.remove(0), prophecise.0.remove(0)))
                    } else {
                        None
                    };

                    (assuming, from, extract, proph_model, prophecise.1)
                })
                .1
            });
        ExtractLemmaTerm {
            uni,
            models: None,
            assuming,
            from,
            extract,
            proph_model,
            prophecise,
        }
    }

    pub(crate) fn build_lemma_proof(&self, expr: ExprId) -> Vec<ProofStep<'tcx>> {
        let expr = self.peel_scope(expr);
        let (_, steps) = self.peel_lvar_bindings(expr, |this, expr| {
            let expr = this.peel_scope(expr);

            let thir::ExprKind::Block { block } = this.thir[expr].kind else {
                return vec![this.proof_step(expr)];
            };
            //  else {
            //
            // };

            this.proof_sequence(block)
        });
        steps
    }

    pub(crate) fn proof_sequence(&self, block: BlockId) -> Vec<ProofStep<'tcx>> {
        let mut steps = Vec::new();

        for stmt in self.thir[block].stmts.iter() {
            match &self.thir[*stmt].kind {
                thir::StmtKind::Expr { expr, .. } => steps.push(self.proof_step(*expr)),
                thir::StmtKind::Let { initializer, .. } => {
                    let is_useless_binder_for_pre_types =
                        initializer.map_or(false, |e| match &self.thir[self.peel_scope(e)].kind {
                            thir::ExprKind::Call { ty, .. } => {
                                // TODO: fix this nightmare
                                match ty.kind() {
                                    TyKind::FnDef(_, subst) => {
                                        (!subst.is_empty()) && subst.type_at(0).is_closure()
                                    }
                                    _ => false,
                                }
                            }
                            _ => false,
                        });

                    if is_useless_binder_for_pre_types {
                        continue;
                    }

                    // continue;
                    steps.push(self.proof_step(initializer.unwrap()));
                    // fatal2!(self.tcx, "assert bindings are currently unsupported")
                }
            };
        }

        if let Some(e) = self.thir[block].expr {
            steps.push(self.proof_step(e))
        }

        steps
    }

    pub(crate) fn proof_step(&self, expr: ExprId) -> ProofStep<'tcx> {
        let expr = self.peel_scope(expr);

        match &self.thir[expr].kind {
            thir::ExprKind::Call { ty, args, .. } => match self.get_stub(*ty) {
                Some(LogicStubs::Package) => {
                    let mut args: Vec<_> = args.iter().map(|a| self.build_assert(*a)).collect();

                    let AssertKind::Call(pre) = args.remove(0).kind else {
                        fatal2!(self.tcx, "expected precondition of package to be a call")
                    };

                    let AssertKind::Call(post) = args.remove(0).kind else {
                        fatal2!(self.tcx, "expected postcondition of package to be a call")
                    };

                    ProofStep::Package { pre, post }
                }
                Some(LogicStubs::Unfold) => {
                    let AssertKind::Call(pre) = self.build_assert(args[0]).kind else {
                        fatal2!(self.tcx, "unfold expects a call")
                    };
                    ProofStep::Unfold { pred: pre }
                }
                Some(LogicStubs::Fold) => {
                    let AssertKind::Call(pre) = self.build_assert(args[0]).kind else {
                        fatal2!(self.tcx, "fold expects a call")
                    };
                    ProofStep::Fold { pred: pre }
                }
                Some(LogicStubs::AssertBind) => {
                    let (vars, assertion) = self.build_assert_bind(args[0]);
                    ProofStep::AssertBind { assertion, vars }
                }
                Some(LogicStubs::Assume) => {
                    let formula = self.build_formula(args[0]);
                    ProofStep::Assume { formula }
                }
                Some(stub) => fatal2!(
                    self.tcx,
                    "unsupported proof step {stub:?} {:?}",
                    &self.thir[expr].kind
                ),
                None => {
                    let ty::FnDef(def_id, substs) = *ty.kind() else {
                        unreachable!()
                    };

                    let args = args.iter().map(|a| self.build_expression(*a)).collect();

                    ProofStep::Call {
                        lemma_call: AssertPredCall {
                            def_id,
                            substs,
                            args,
                        },
                    }
                }
            },
            thir::ExprKind::If {
                cond,
                then,
                else_opt,
                ..
            } => {
                let cond = self.build_expression(*cond);
                let thir::ExprKind::Block { block } = self.thir[self.peel_scope(*then)].kind else {
                    fatal2!(self.tcx, "expected block in proof")
                };

                let Some(else_opt) = else_opt else {
                    fatal2!(self.tcx, "expected block in proof")
                };

                let thir::ExprKind::Block { block: else_block } =
                    self.thir[self.peel_scope(*else_opt)].kind
                else {
                    fatal2!(self.tcx, "expected block in proof")
                };

                let t_branch = self.proof_sequence(block);
                let f_branch = self.proof_sequence(else_block);

                ProofStep::If {
                    cond,
                    t_branch,
                    f_branch,
                }
            }
            s => fatal2!(self.tcx, "unsupported proof step {s:?}"),
        }
    }

    fn build_assert_bind(&self, expr: ExprId) -> (Vec<Symbol>, Assert<'tcx>) {
        match &self.thir[expr].kind {
            thir::ExprKind::Scope { value, .. } => self.build_assert_bind(*value),
            thir::ExprKind::Closure(box ClosureExpr {
                closure_id,
                args: UpvarArgs::Closure(_),
                ..
            }) => {
                let names = self.tcx.fn_arg_names(*closure_id);

                let (thir, expr) = self.tcx.thir_body(closure_id).unwrap();

                let body = Self {
                    thir: thir.borrow().clone(),
                    tcx: self.tcx,
                }
                .peel_lvar_bindings(expr, |this, expr| this.build_assert(expr));
                (names.iter().map(|i| i.name).collect(), body.1)
            }
            kind => self
                .tcx
                .dcx()
                .fatal(format!("Unexpected quantified form: {:?}", kind)),
        }
    }

    pub(crate) fn build_assert(&self, expr: ExprId) -> Assert<'tcx> {
        Assert {
            kind: self.build_assert_kind(expr),
        }
    }

    fn build_quantified_assert(&self, expr: ExprId) -> (Vec<(Symbol, Ty<'tcx>)>, Assert<'tcx>) {
        self.peel_lvar_bindings(expr, |this, expr| this.build_assert(expr))
    }

    pub fn build_predicate(&self, expr: ExprId) -> Predicate<'tcx> {
        let defs = self.resolve_definitions(expr);
        let asserts = defs
            .into_iter()
            .map(|eid| self.build_quantified_assert(eid))
            .map(|(vars, asrt)| {
                let asrt = self
                    .thir
                    .params
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, param)| {
                        Some((idx, param.ty, self.pattern_term(param.pat.as_ref()?)))
                    })
                    .fold(asrt, |body, (idx, ty, pattern)| match pattern {
                        Pattern::Binder(_) | Pattern::Wildcard(_) => body,
                        _ => {
                            let arg = Expr {
                                ty,
                                kind: ExprKind::Var {
                                    id: anonymous_param_symbol(idx),
                                },
                            };
                            Assert {
                                kind: AssertKind::Let {
                                    pattern,
                                    arg,
                                    body: Box::new(body),
                                },
                            }
                        }
                    });

                (vars, asrt)
            });

        Predicate {
            disjuncts: asserts.collect(),
        }
    }

    pub fn build_spec(&self, spec_id: DefId, expr: ExprId) -> SpecTerm<'tcx> {
        let (mut uni, (pre, posts)) = self.peel_lvar_bindings(expr, |this, expr| {
            let expr = this.peel_scope(expr);
            let thir::ExprKind::Call {
                ty, fun: _, args, ..
            } = &this.thir[expr].kind
            else {
                unreachable!("ill formed specification block {:?}", this.thir[expr])
            };

            let Some(LogicStubs::Spec) = this.get_stub(*ty) else {
                unreachable!("ill formed specification block")
            };

            let pre = this.build_assert(args[0]);

            let thir::ExprKind::Array { fields } = &this.thir[this.peel_scope(args[1])].kind else {
                unreachable!(
                    "Expected postcondition to be an array, but got {:?}",
                    this.thir[args[1]].kind
                );
            };

            let posts: Vec<_> = fields
                .iter()
                .map(|post_id| {
                    this.peel_lvar_bindings(*post_id, |this, expr| this.build_assert(expr))
                })
                .collect();

            (pre, posts)
        });

        // eprintln!("params: {:?}", self.thir.params);
        let pre = self
            .thir
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, param)| {
                Some((idx, param.ty, self.pattern_term(&*param.pat.as_ref()?)))
            })
            .fold(pre, |body, (idx, ty, pattern)| match pattern {
                Pattern::Binder(_) | Pattern::Wildcard(_) => body,
                _ => {
                    let arg = Expr {
                        ty,
                        kind: ExprKind::Var {
                            id: anonymous_param_symbol(idx),
                        },
                    };
                    Assert {
                        kind: AssertKind::Let {
                            pattern,
                            arg,
                            body: Box::new(body),
                        },
                    }
                }
            });

        // Lemmas encode their specifications using closures and do weird things with lvar scopes so we can
        // use them in the body of the proof.
        // As a result, we also store the lvars in the closure signature and need to read them out from here rather than
        // a call to `instantiate_lvars`.
        if self.tcx.is_closure_like(spec_id) {
            let (inputs, _) = inputs_and_output(self.tcx, spec_id);

            let inputs: Vec<_> = inputs.skip(1).map(|(i, ty)| (i.name, ty)).collect();

            uni.extend(inputs);
        }

        SpecTerm {
            uni,
            pre,
            posts,
            trusted: false,
        }
    }

    fn resolve_definitions(&self, e: ExprId) -> Vec<ExprId> {
        let expr = &self.thir.exprs[e];
        match &expr.kind {
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.resolve_definitions(*value),
            thir::ExprKind::Use { source } => self.resolve_definitions(*source),
            thir::ExprKind::Block { block } => {
                let block = &self.thir.blocks[*block];
                assert!(block.stmts.is_empty());

                self.resolve_definitions(block.expr.unwrap())
            }

            thir::ExprKind::Call { ty, args, .. }
                if self.get_stub(*ty) == Some(LogicStubs::PredDefs) =>
            {
                assert!(args.len() == 1, "Defs call must have one argument");
                self.resolve_array(args[0])
            }
            e => unreachable!("{e:?}"),
        }
    }

    pub(crate) fn resolve_array(&self, e: ExprId) -> Vec<ExprId> {
        let expr = &self.thir[e];
        match &expr.kind {
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.resolve_array(*value),
            thir::ExprKind::Use { source } => self.resolve_array(*source),
            thir::ExprKind::Block { block } => {
                let block = &self.thir[*block];
                assert!(block.stmts.is_empty());
                self.resolve_array(block.expr.unwrap())
            }
            thir::ExprKind::Array { fields } => fields.to_vec(),
            _ => unreachable!(),
        }
    }

    fn build_assert_kind(&self, id: ExprId) -> AssertKind<'tcx> {
        let expr = &self.thir[id];
        if !self.is_assertion_ty(expr.ty) {
            self.tcx.dcx().span_fatal(
                expr.span,
                format!("{:?} is not the assertion type: {:?}", expr.ty, expr),
            )
        }
        match &expr.kind {
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.build_assert_kind(*value),
            thir::ExprKind::Block { block } if self.thir[*block].stmts.is_empty() => {
                self.build_assert_kind(self.thir[*block].expr.unwrap())
            }
            thir::ExprKind::Use { source } => self.build_assert_kind(*source),
            thir::ExprKind::Call {
                ty, fun: _, args, ..
            } => {
                match self.get_stub(*ty) {
                    Some(LogicStubs::AssertPure) => {
                        let formula = self.build_formula(args[0]);
                        AssertKind::Formula { formula }
                    }
                    Some(LogicStubs::AssertStar) => {
                        let mut args: Vec<_> = args.iter().map(|a| self.build_assert(*a)).collect();

                        AssertKind::Star {
                            left: Box::new(args.remove(0)),
                            right: Box::new(args.remove(0)),
                        }
                    }
                    Some(LogicStubs::AssertEmp) => AssertKind::Emp,
                    Some(LogicStubs::AssertWand) => {
                        let lhs = self.build_assert(args[0]);
                        let rhs = self.build_assert(args[1]);

                        AssertKind::Wand {
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        }
                    }
                    Some(LogicStubs::AssertPointsTo) => {
                        let src = self.build_expression(args[0]);
                        let tgt = self.build_expression(args[1]);

                        AssertKind::PointsTo { src, tgt }
                    }
                    // Other core predicates
                    Some(LogicStubs::AssertObservation) => {
                        let expr = self.build_expression(args[0]);
                        AssertKind::Observation { expr }
                    }
                    Some(LogicStubs::AssertPointsToSlice) => {
                        let src = self.build_expression(args[0]);
                        let size = self.build_expression(args[1]);
                        let pointees = self.build_expression(args[2]);

                        // TODO unify with PointsTo
                        AssertKind::PointsToSlice {
                            src,
                            size,
                            pointees,
                        }
                    }
                    Some(LogicStubs::AssertUninit) => {
                        let pointer = self.build_expression(args[0]);

                        AssertKind::Uninit { pointer }
                    }
                    Some(LogicStubs::AssertManyUninits) => {
                        let pointer = self.build_expression(args[0]);

                        let size = self.build_expression(args[1]);

                        AssertKind::ManyUninits { pointer, size }
                    }
                    Some(LogicStubs::AssertMaybeUninit) => {
                        let pointer = self.build_expression(args[0]);
                        let pointee = self.build_expression(args[1]);

                        AssertKind::MaybeUninit { pointer, pointee }
                    }
                    Some(LogicStubs::AssertManyMaybeUninits) => {
                        let pointer = self.build_expression(args[0]);

                        let size = self.build_expression(args[1]);
                        let pointees = self.build_expression(args[2]);
                        AssertKind::ManyMaybeUninits {
                            pointer,
                            pointees,
                            size,
                        }
                    }
                    Some(LogicStubs::ProphecyObserver) => {
                        let prophecy = self.build_expression(args[0]);
                        let model = self.build_expression(args[1]);
                        AssertKind::ProphecyObserver { prophecy, model }
                    }
                    Some(LogicStubs::ProphecyController) => {
                        let prophecy = self.build_expression(args[0]);
                        let model = self.build_expression(args[1]);
                        AssertKind::ProphecyController { prophecy, model }
                    }
                    Some(LogicStubs::OwnPred) | None => {
                        let ty::FnDef(def_id, substs) = *ty.kind() else {
                            unreachable!()
                        };

                        let args = args.iter().map(|a| self.build_expression(*a)).collect();

                        AssertKind::Call(AssertPredCall {
                            def_id,
                            substs,
                            args,
                        })
                    }
                    Some(s) => self
                        .tcx
                        .dcx()
                        .fatal(format!("Unsupported logic stub in assert {s:?}")),
                    // () => (),
                }
            }
            _ => self
                .tcx
                .dcx()
                .fatal(format!("Can't parse assertion yet: {:?}", expr)),
        }
    }

    fn get_stub(&self, ty: Ty<'tcx>) -> Option<LogicStubs> {
        LogicStubs::for_fn_def_ty(ty, self.tcx)
    }

    fn is_assertion_ty(&self, ty: Ty<'tcx>) -> bool {
        super::builtins::is_assertion_ty(ty, self.tcx)
    }

    fn is_formula_ty(&self, ty: Ty<'tcx>) -> bool {
        super::builtins::is_formula_ty(ty, self.tcx)
    }

    fn build_formula(&self, id: ExprId) -> Formula<'tcx> {
        let id = self.peel_scope(id);
        let expr = &self.thir[id];
        if !self.is_formula_ty(expr.ty) {
            self.tcx
                .dcx()
                .fatal(format!("{:?} is not the formula type", expr.ty))
        }

        match &expr.kind {
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.build_formula(*value),
            thir::ExprKind::Use { source } => self.build_formula(*source),
            thir::ExprKind::Call {
                ty, fun: _, args, ..
            } => {
                let stub = self.get_stub(*ty);
                match stub {
                    Some(LogicStubs::FormulaForall) => self.build_forall_body(args[0]),
                    _ => Formula {
                        bound_vars: Vec::new(),
                        body: self.build_formula_body(id),
                    },
                }
            }
            _ => self
                .tcx
                .dcx()
                .fatal(format!("Unsupported formula: {:?}", expr)),
        }
    }

    fn build_forall_body(&self, id: ExprId) -> Formula<'tcx> {
        match &self.thir[id].kind {
            thir::ExprKind::Scope { value, .. } => self.build_forall_body(*value),
            thir::ExprKind::Closure(box ClosureExpr {
                closure_id,
                args: UpvarArgs::Closure(args),
                ..
            }) => {
                let name = self.tcx.fn_arg_names(*closure_id)[0];
                let ty = args
                    .as_closure()
                    .sig()
                    .input(0)
                    .skip_binder()
                    .tuple_fields()[0];
                let (thir, expr) = self.tcx.thir_body(closure_id).unwrap();
                let body = Self {
                    thir: thir.borrow().clone(),
                    tcx: self.tcx,
                }
                .build_formula_body(expr);
                Formula {
                    bound_vars: vec![(name.name, ty)],
                    body,
                }
            }
            kind => self
                .tcx
                .dcx()
                .fatal(format!("Unexpected quantified form: {:?}", kind)),
        }
    }

    fn build_quantified_body<F: Fn((Symbol, Ty<'tcx>), Box<Expr<'tcx>>) -> ExprKind<'tcx>>(
        &self,
        id: ExprId,
        mk_quant: F,
    ) -> ExprKind<'tcx> {
        match &self.thir[id].kind {
            thir::ExprKind::Scope { value, .. } => self.build_quantified_body(*value, mk_quant),
            thir::ExprKind::Closure(box ClosureExpr {
                closure_id,
                args: UpvarArgs::Closure(args),
                ..
            }) => {
                let name = self.tcx.fn_arg_names(*closure_id)[0];
                let ty = args
                    .as_closure()
                    .sig()
                    .input(0)
                    .skip_binder()
                    .tuple_fields()[0];
                let (thir, expr) = self.tcx.thir_body(closure_id).unwrap();
                let body = Self {
                    thir: thir.borrow().clone(),
                    tcx: self.tcx,
                }
                .build_expression(expr);
                mk_quant((name.name, ty), Box::new(body))
            }
            kind => self
                .tcx
                .dcx()
                .fatal(format!("Unexpected quantified form: {:?}", kind)),
        }
    }

    fn build_formula_body(&self, id: ExprId) -> FormulaKind<'tcx> {
        let id = self.peel_scope(id);
        let expr = &self.thir[id];
        if !self.is_formula_ty(expr.ty) {
            fatal2!(self.tcx, "{:?} is not the formula type", expr.ty)
        }

        match &expr.kind {
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.build_formula_body(*value),

            thir::ExprKind::Use { source } => self.build_formula_body(*source),
            thir::ExprKind::Call {
                ty, fun: _, args, ..
            } => {
                let stub = self.get_stub(*ty);
                match stub {
                    Some(LogicStubs::FormulaEqual) => {
                        let left = self.build_expression(args[0]);
                        let right = self.build_expression(args[1]);
                        FormulaKind::EOp {
                            left: Box::new(left),
                            op: EOp::Eq,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaLess) => {
                        let left = self.build_expression(args[0]);
                        let right = self.build_expression(args[1]);
                        FormulaKind::EOp {
                            left: Box::new(left),
                            op: EOp::Lt,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaLessEq) => {
                        let left = self.build_expression(args[0]);
                        let right = self.build_expression(args[1]);
                        FormulaKind::EOp {
                            left: Box::new(left),
                            op: EOp::Le,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaAnd) => {
                        let left = self.build_formula_body(args[0]);
                        let right = self.build_formula_body(args[1]);
                        FormulaKind::FOp {
                            left: Box::new(left),
                            op: FOp::And,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaOr) => {
                        let left = self.build_formula_body(args[0]);
                        let right = self.build_formula_body(args[1]);
                        FormulaKind::FOp {
                            left: Box::new(left),
                            op: FOp::Or,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaNeg) => {
                        let form = self.build_formula_body(args[0]);
                        FormulaKind::Neg {
                            form: Box::new(form),
                        }
                    }
                    Some(LogicStubs::FormulaNotEqual) => {
                        let left = self.build_expression(args[0]);
                        let right = self.build_expression(args[1]);
                        FormulaKind::EOp {
                            left: Box::new(left),
                            op: EOp::Ne,
                            right: Box::new(right),
                        }
                    }
                    Some(LogicStubs::FormulaImplication) => {
                        let left = self.build_formula_body(args[0]);
                        let right = self.build_formula_body(args[1]);
                        FormulaKind::FOp {
                            left: Box::new(left),
                            op: FOp::Impl,
                            right: Box::new(right),
                        }
                    }
                    _ => self
                        .tcx
                        .dcx()
                        .fatal(format!("Unsupported formula: {:?}", expr)),
                }
            }
            _ => self
                .tcx
                .dcx()
                .fatal(format!("Unsupported formula: {:?}", expr)),
        }
    }

    fn build_expression(&self, id: ExprId) -> Expr<'tcx> {
        Expr {
            ty: self.thir[id].ty,
            kind: self.build_expression_kind(id),
        }
    }

    fn compile_constant(&self, cst: ConstValue<'tcx>, ty: Ty<'tcx>) -> ExprKind<'tcx> {
        match (cst, ty.kind()) {
            (ConstValue::ZeroSized, _) => ExprKind::ZST,
            (ConstValue::Scalar(Scalar::Int(sci)), TyKind::Int(..)) => {
                let i = sci
                    .try_to_int(sci.size())
                    .expect("Cannot fail because we chose the right size");
                ExprKind::Integer { value: i.into() }
            }
            (ConstValue::Scalar(Scalar::Int(sci)), TyKind::Uint(..)) => {
                let i = sci
                    .try_to_uint(sci.size())
                    .expect("Cannot fail because we chose the right size");
                ExprKind::Integer { value: i.into() }
            }
            _ => self
                .tcx
                .dcx()
                .fatal(format!("Cannot encore constant {:?} of type {:?}", cst, ty)),
        }
    }

    fn build_expression_kind(&self, id: ExprId) -> ExprKind<'tcx> {
        let expr = &self.thir[id];

        match &expr.kind {
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.build_expression_kind(*value),
            thir::ExprKind::Use { source } => self.build_expression_kind(*source),
            thir::ExprKind::UpvarRef { var_hir_id, .. } => ExprKind::Var {
                id: self.tcx.hir().name(var_hir_id.0),
            },
            thir::ExprKind::VarRef { id } => ExprKind::Var {
                id: self.tcx.hir().name(id.0),
            },
            thir::ExprKind::NamedConst {
                def_id,
                args,
                user_ty: _,
            } => {
                if !args.is_empty() {
                    self.tcx
                        .dcx()
                        .fatal(format!("Cannot evaluate this constant yet: {:?}", def_id));
                };
                let cst = self.tcx.const_eval_poly(*def_id).unwrap_or_else(|_| {
                    self.tcx
                        .dcx()
                        .fatal(format!("Cannot evaluate this constant yet: {:?}", def_id))
                });

                self.compile_constant(cst, expr.ty)
            }
            thir::ExprKind::Adt(box AdtExpr {
                adt_def,
                variant_index,
                fields,
                args,
                base,
                ..
            }) => {
                assert!(base.is_none());

                let mut fields_with_idx: Vec<(FieldIdx, _)> = fields
                    .iter()
                    .map(|f| (f.name, self.build_expression(f.expr)))
                    .collect();
                fields_with_idx.sort_by(|(f1, _), (f2, _)| f1.cmp(f2));
                let fields: Vec<_> = fields_with_idx.into_iter().map(|(_, e)| e).collect();

                ExprKind::Constructor {
                    def_id: adt_def.did(),
                    _args: args,
                    variant_index: *variant_index,
                    fields,
                }
            }
            thir::ExprKind::Tuple { fields } => {
                let fields = fields.iter().map(|f| self.build_expression(*f)).collect();

                ExprKind::Tuple { fields }
            }
            thir::ExprKind::Borrow {
                borrow_kind: b @ (BorrowKind::Mut { .. } | BorrowKind::Shared),
                arg,
            } => {
                let inner_id = self.peel_scope(*arg);
                let arg = &self.thir[inner_id];

                match arg.kind {
                    thir::ExprKind::Deref { arg: e } if matches!(b, BorrowKind::Mut { .. }) => {
                        let inner_ty = self.thir[e].ty;
                        if crate::logic::ty_utils::is_mut_ref(inner_ty) {
                            // Reborrowing a mut-ref, it is already of the right shape
                            self.build_expression_kind(e)
                        } else if inner_ty.is_any_ptr() {
                            // Reborrowing e.g. a raw pointer, we need to add the prophecy
                            let inner = self.build_expression(e);
                            ExprKind::PtrToMutRef {
                                ptr: Box::new(inner),
                            }
                        } else {
                            self.tcx.dcx().fatal(format!("Reborrowing something of type {:?} that is not a pointer in logic?", inner_ty));
                        }
                    }
                    thir::ExprKind::Deref { arg: e } => self.build_expression_kind(e),
                    thir::ExprKind::Field { lhs, name, .. } => {
                        let thir::ExprKind::Deref { arg } = &self.thir[self.peel_scope(lhs)].kind
                        else {
                            todo!("Gilsonite field expression that is not deref")
                        };

                        let lhs = self.build_expression(*arg);
                        ExprKind::Field {
                            lhs: Box::new(lhs),
                            field: name,
                        }
                    }
                    // HACK
                    _ if *b == BorrowKind::Shared => self.build_expression_kind(inner_id),
                    _ => todo!("unsupported {arg:?}"),
                }
            }
            thir::ExprKind::Literal { lit, neg: false } => match lit.node {
                LitKind::Int(i, _) => ExprKind::Integer {
                    value: i.get().into(),
                },

                LitKind::Bool(true) => ExprKind::True,
                LitKind::Bool(false) => ExprKind::False,
                _ => self
                    .tcx
                    .dcx()
                    .fatal(format!("Unsupported literal {:?}", expr)),
            },
            thir::ExprKind::Field {
                lhs,
                variant_index: _,
                name,
            } => {
                let lhs = self.build_expression(*lhs);
                ExprKind::Field {
                    lhs: Box::new(lhs),
                    field: *name,
                }
            }
            thir::ExprKind::Binary { op, lhs, rhs } => {
                let lhs = self.build_expression(*lhs);
                let rhs = self.build_expression(*rhs);
                let op = match op {
                    mir::BinOp::Add => BinOp::Add,
                    mir::BinOp::Sub => BinOp::Sub,
                    mir::BinOp::Shl => BinOp::Shl,
                    mir::BinOp::Div => BinOp::Div,
                    mir::BinOp::Mul => BinOp::Mul,
                    mir::BinOp::Eq => BinOp::Eq,
                    mir::BinOp::Lt => BinOp::Lt,
                    mir::BinOp::Le => BinOp::Le,
                    mir::BinOp::Ge => BinOp::Ge,
                    mir::BinOp::Gt => BinOp::Gt,
                    mir::BinOp::Rem => BinOp::Rem,
                    _ => todo!("Gilsonite Expr Kind: {:?}", op),
                };

                ExprKind::BinOp {
                    left: Box::new(lhs),
                    op,
                    right: Box::new(rhs),
                }
            }
            thir::ExprKind::LogicalOp { op, lhs, rhs } => {
                let lhs = self.build_expression(*lhs);
                let rhs = self.build_expression(*rhs);
                let op = match op {
                    LogicalOp::And => BinOp::And,
                    LogicalOp::Or => BinOp::Or,
                };

                ExprKind::BinOp {
                    left: Box::new(lhs),
                    op,
                    right: Box::new(rhs),
                }
            }
            thir::ExprKind::Cast { source } => {
                let source = self.build_expression(*source);
                if source.ty.is_integral() && expr.ty.is_integral() {
                    if let ExprKind::Integer {
                        value: EncDeBigInt(bigint),
                    } = &source.kind
                    {
                        let (low, high) = crate::utils::ty::int_bounds(expr.ty, self.tcx);
                        if bigint < &low || &high < bigint {
                            self.tcx.dcx().fatal("Casting: Overflow!")
                        }
                    };
                    return source.kind;
                };
                self.tcx
                    .dcx()
                    .fatal("To implement in logic: cast that is not int-to-int")
            }
            thir::ExprKind::Unary { op, arg } => {
                let arg = self.build_expression(*arg);

                ExprKind::UnOp {
                    op: *op,
                    arg: Box::new(arg),
                }
            }
            thir::ExprKind::Call {
                ty, fun: _, args, ..
            } => {
                let stub = self.get_stub(*ty);
                match stub {
                    Some(LogicStubs::FormulaEqual) => {
                        assert!(args.len() == 2, "Equal call must have two arguments");
                        let left = Box::new(self.build_expression(args[0]));
                        let right = Box::new(self.build_expression(args[1]));

                        ExprKind::BinOp {
                            left,
                            op: BinOp::Eq,
                            right,
                        }
                    }
                    Some(LogicStubs::ExprEq) => {
                        assert!(args.len() == 2, "Equal call must have two arguments");
                        let left = Box::new(self.build_expression(args[0]));
                        let right = Box::new(self.build_expression(args[1]));

                        ExprKind::BinOp {
                            left,
                            op: BinOp::Eq,
                            right,
                        }
                    }
                    Some(LogicStubs::ExprNe) => {
                        assert!(args.len() == 2, "Equal call must have two arguments");
                        let left = Box::new(self.build_expression(args[0]));
                        let right = Box::new(self.build_expression(args[1]));

                        ExprKind::BinOp {
                            left,
                            op: BinOp::Ne,
                            right,
                        }
                    }
                    Some(LogicStubs::ExprImpl) => {
                        assert!(args.len() == 2, "Equal call must have two arguments");
                        let left = Box::new(self.build_expression(args[0]));
                        let right = Box::new(self.build_expression(args[1]));

                        ExprKind::BinOp {
                            left,
                            op: BinOp::Impl,
                            right,
                        }
                    }
                    Some(LogicStubs::FormulaLessEq) => {
                        assert!(args.len() == 2, "Equal call must have two arguments");
                        let left = Box::new(self.build_expression(args[0]));
                        let right = Box::new(self.build_expression(args[1]));

                        ExprKind::BinOp {
                            left,
                            op: BinOp::Le,
                            right,
                        }
                    }
                    Some(LogicStubs::FormulaLess) => {
                        assert!(args.len() == 2, "Equal call must have two arguments");
                        let left = Box::new(self.build_expression(args[0]));
                        let right = Box::new(self.build_expression(args[1]));

                        ExprKind::BinOp {
                            left,
                            op: BinOp::Lt,
                            right,
                        }
                    }
                    Some(LogicStubs::SeqNil) => ExprKind::SeqNil,
                    Some(
                        a @ (LogicStubs::SeqAppend
                        | LogicStubs::SeqPrepend
                        | LogicStubs::SeqConcat
                        | LogicStubs::SeqHead
                        | LogicStubs::SeqLast
                        | LogicStubs::SeqTail
                        | LogicStubs::SeqLen
                        | LogicStubs::SeqAt
                        | LogicStubs::SeqSub
                        | LogicStubs::SeqRepeat),
                    ) => {
                        let args = args.iter().map(|a| self.build_expression(*a)).collect();
                        let op = match a {
                            LogicStubs::SeqAppend => SeqOp::Append,
                            LogicStubs::SeqPrepend => SeqOp::Prepend,
                            LogicStubs::SeqConcat => SeqOp::Concat,
                            LogicStubs::SeqHead => SeqOp::Head,
                            LogicStubs::SeqLast => SeqOp::Last,
                            LogicStubs::SeqTail => SeqOp::Tail,
                            LogicStubs::SeqLen => SeqOp::Len,
                            LogicStubs::SeqAt => SeqOp::At,
                            LogicStubs::SeqSub => SeqOp::Sub,
                            LogicStubs::SeqRepeat => SeqOp::Repeat,
                            _ => unreachable!(),
                        };
                        ExprKind::SeqOp { op, args }
                    }
                    Some(LogicStubs::ExprExists) => {
                        self.build_quantified_body(args[0], ExprKind::mk_exists)
                    }
                    Some(LogicStubs::ExprForall) => {
                        self.build_quantified_body(args[0], ExprKind::mk_forall)
                    }
                    None => {
                        let ty::FnDef(def_id, substs) = *ty.kind() else {
                            unreachable!()
                        };

                        let args = args.iter().map(|a| self.build_expression(*a)).collect();

                        ExprKind::Call {
                            def_id,
                            substs,
                            args,
                        }
                    }
                    Some(LogicStubs::MutRefGetProphecy) => {
                        let mut_ref = Box::new(self.build_expression(args[0]));
                        ExprKind::GetProphecy { mut_ref }
                    }
                    Some(LogicStubs::ProphecyGetValue) => {
                        let mut_ref = Box::new(self.build_expression(args[0]));
                        ExprKind::GetValue { mut_ref }
                    }
                    Some(LogicStubs::MutRefSetProphecy) => {
                        let mut_ref = Box::new(self.build_expression(args[0]));
                        let prophecy = Box::new(self.build_expression(args[1]));
                        ExprKind::SetProphecy { mut_ref, prophecy }
                    }
                    Some(a) => self
                        .tcx
                        .dcx()
                        .fatal(format!("{:?} unsupported stub in expression", a)),
                }
            }
            _ => self
                .tcx
                .dcx()
                .fatal(format!("Unsupported expression: {:?}", expr)),
        }
    }

    fn pattern_term(&self, pat: &Pat<'tcx>) -> Pattern<'tcx> {
        use thir::PatKind;
        match &pat.kind {
            PatKind::Wild => Pattern::Wildcard(pat.ty),
            PatKind::Binding { name, .. } => Pattern::Binder(*name),
            PatKind::Variant {
                subpatterns,
                adt_def,
                variant_index,
                args,
                ..
            } => {
                let mut fields: Vec<_> = subpatterns
                    .iter()
                    .map(|pat| (pat.field, self.pattern_term(&pat.pattern)))
                    .collect();
                fields.sort_by_key(|f| f.0);

                let raw_fields = &adt_def.variants()[0usize.into()].fields;
                let defaults = raw_fields
                    .iter()
                    .enumerate()
                    .map(|(i, f)| (i.into(), Pattern::Wildcard(f.ty(self.tcx, args))));

                let fields = defaults
                    .merge_join_by(fields, |i: &(FieldIdx, _), j: &(FieldIdx, _)| i.0.cmp(&j.0))
                    .map(|el| el.reduce(|_, a| a).1)
                    .collect();

                Pattern::Constructor {
                    adt: adt_def.variants()[*variant_index].def_id,
                    substs: args,
                    variant: *variant_index,
                    fields,
                }
            }
            PatKind::Leaf { subpatterns } => {
                let mut fields: Vec<_> = subpatterns
                    .iter()
                    .map(|pat| (pat.field, self.pattern_term(&pat.pattern)))
                    .collect();
                fields.sort_by_key(|f| f.0);

                if matches!(pat.ty.kind(), TyKind::Tuple(_)) {
                    let fields = fields.into_iter().map(|a| a.1).collect();
                    Pattern::Tuple(fields)
                } else {
                    let (adt_def, substs) = if let TyKind::Adt(def, substs) = pat.ty.kind() {
                        (def, substs)
                    } else {
                        unreachable!()
                    };

                    let raw_fields = &adt_def.variants()[0usize.into()].fields;
                    let defaults = raw_fields
                        .iter()
                        .enumerate()
                        .map(|(i, f)| (i.into(), Pattern::Wildcard(f.ty(self.tcx, substs))));

                    let fields = defaults
                        .merge_join_by(fields, |i: &(FieldIdx, _), j| i.0.cmp(&j.0))
                        .map(|el| el.reduce(|_, a| a).1)
                        .collect();
                    Pattern::Constructor {
                        adt: adt_def.variants()[0usize.into()].def_id,
                        substs,
                        variant: 0u32.into(),
                        fields,
                    }
                }
            }
            PatKind::Deref { subpattern } => {
                if !(pat.ty.is_box() || pat.ty.ref_mutability() == Some(Mutability::Not)) {
                    fatal2!(self.tcx, "unsupported pattern")
                }

                self.pattern_term(subpattern)
            }
            PatKind::Constant { value } => {
                if !pat.ty.is_bool() {
                    fatal2!(self.tcx, "non-boolean constant patterns are unsupported",)
                }
                Pattern::Boolean(value.try_to_bool().unwrap())
            }
            ref pk => todo!("lower_pattern: unsupported pattern kind {:?}", pk),
        }
    }

    fn peel_scope(&self, e: ExprId) -> ExprId {
        let expr = &self.thir.exprs[e];
        match &expr.kind {
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.peel_scope(*value),
            thir::ExprKind::Use { source } => self.peel_scope(*source),
            thir::ExprKind::Block { block }
                if self.thir[*block].stmts.is_empty() && self.thir[*block].expr.is_some() =>
            {
                self.peel_scope(self.thir[*block].expr.unwrap())
            }
            _ => e,
        }
    }

    /// Removes any bindings for lvars surrounding an assertion and adds them to the environment.
    fn peel_lvar_bindings<A>(
        &self,
        mut e: ExprId,
        mut k: impl FnMut(&Self, ExprId) -> A,
    ) -> (Vec<(Symbol, Ty<'tcx>)>, A) {
        e = self.peel_scope(e);

        match &self.thir[e].kind {
            thir::ExprKind::Call { ty, args, .. }
                if self.get_stub(*ty) == Some(LogicStubs::InstantiateLVars) =>
            {
                let thir::ExprKind::Closure(clos) = &self.thir[self.peel_scope(args[0])].kind
                else {
                    unreachable!()
                };

                let mut lvars = Vec::new();
                for (nm, ty) in fn_args_and_tys(self.tcx, clos.closure_id.to_def_id()) {
                    lvars.push((nm, ty));
                }

                let (thir, expr) = self.tcx.thir_body(clos.closure_id).unwrap();

                let inner = Self::new(thir.borrow().clone(), self.tcx);
                let x = k(&inner, expr);

                (lvars, x)
            }
            thir::ExprKind::Block { block }
                if self.thir[*block].stmts.is_empty() && self.thir[*block].expr.is_some() =>
            {
                let block = &self.thir[*block];

                // let StmtKind::Expr { expr, .. }  = thir[block.stmts[0]].kind else { panic!() };
                self.peel_lvar_bindings(block.expr.unwrap(), k)
            }
            _ => (Vec::new(), k(self, e)),
        }
    }
}

#[allow(dead_code)]
struct PrintExpr<'a, 'tcx>(&'a Thir<'tcx>, ExprId);

impl std::fmt::Display for PrintExpr<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        print_thir_expr(f, self.0, self.1)
    }
}

#[allow(dead_code)]
fn print_thir_expr(
    fmt: &mut std::fmt::Formatter,
    thir: &Thir,
    expr_id: ExprId,
) -> std::fmt::Result {
    match &thir[expr_id].kind {
        thir::ExprKind::Call { fun, args, ty, .. } => {
            print_thir_expr(fmt, thir, *fun)?;
            let TyKind::FnDef(_, sub) = ty.kind() else {
                unreachable!()
            };
            write!(fmt, "<{:?}>", sub)?;
            write!(fmt, "(")?;
            for a in args.iter() {
                print_thir_expr(fmt, thir, *a)?;
                write!(fmt, ",")?;
            }
            write!(fmt, ")")?;
        }
        thir::ExprKind::Deref { arg } => {
            write!(fmt, "* ")?;
            print_thir_expr(fmt, thir, *arg)?;
        }
        thir::ExprKind::Borrow { borrow_kind, arg } => {
            match borrow_kind {
                BorrowKind::Shared => write!(fmt, "& ")?,
                BorrowKind::Fake(..) => write!(fmt, "&fake ")?,
                BorrowKind::Mut { .. } => write!(fmt, "&mut ")?,
            };

            print_thir_expr(fmt, thir, *arg)?;
        }
        thir::ExprKind::Field {
            lhs,
            variant_index,
            name,
        } => {
            print_thir_expr(fmt, thir, *lhs)?;
            let ty = thir[expr_id].ty;
            let (var_name, field_name) = match ty.kind() {
                TyKind::Adt(def, _) => {
                    let var = &def.variants()[*variant_index];
                    (var.name.to_string(), var.fields[*name].name.to_string())
                }
                TyKind::Tuple(_) => ("_".into(), format!("{name:?}")),
                _ => ("closure_field".into(), "closure_field".into()),
            };

            write!(fmt, " as {var_name} . {field_name}")?;
        }
        thir::ExprKind::Index { lhs, index } => {
            print_thir_expr(fmt, thir, *lhs)?;
            write!(fmt, "[")?;
            print_thir_expr(fmt, thir, *index)?;
            write!(fmt, "]")?;
        }
        thir::ExprKind::ZstLiteral { .. } => match thir[expr_id].ty.kind() {
            TyKind::FnDef(id, _) => write!(fmt, "{id:?}")?,
            _ => write!(fmt, "zst")?,
        },
        thir::ExprKind::Literal { lit, neg } => {
            if *neg {
                write!(fmt, "-")?;
            }

            write!(fmt, "{}", lit.node)?;
        }
        thir::ExprKind::Use { source } => print_thir_expr(fmt, thir, *source)?,
        thir::ExprKind::VarRef { id } => {
            write!(fmt, "{:?}", id.0)?;
        }
        thir::ExprKind::Scope { value, .. } => {
            print_thir_expr(fmt, thir, *value)?;
        }
        _ => {
            write!(fmt, "{:?}", thir[expr_id])?;
        }
    }
    Ok(())
}
