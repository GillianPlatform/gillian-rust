use std::collections::HashMap;

use itertools::Itertools;
use pearlite_syn::*;
use syn::{
    spanned::Spanned, BinOp, Error, ExprPath, Ident, Member, Pat, PatIdent, PatPath, PatStruct,
    PatTuple, PatTupleStruct, PatWild, Path, QSelf, UnOp,
};

#[derive(Clone, Debug)]
enum CoreTerm {
    Call(ExprPath, Vec<CoreTerm>),
    MethodCall(Box<CoreTerm>, Ident, Vec<CoreTerm>),
    BinOp(Box<CoreTerm>, BinOp, Box<CoreTerm>),
    UnOp(UnOp, Box<CoreTerm>),
    Final(Box<CoreTerm>),
    Model(Box<CoreTerm>),
    Let(Pat, Box<CoreTerm>, Box<CoreTerm>),
    Match(Box<CoreTerm>, Vec<(Pat, Box<CoreTerm>)>),
    Constructor(ConstructorKind),
    Var(VarKind),
}
#[derive(Clone, Debug)]
enum ConstructorKind {
    Tuple(Vec<CoreTerm>),
    Struct {
        qself: Option<QSelf>,
        path: Path,
        fields: Vec<(Member, CoreTerm)>,
    },
    TupleStruct {
        qself: Option<QSelf>,
        path: Path,
        elems: Vec<CoreTerm>,
    },
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum VarKind {
    Source(Ident),
    DeBruijn(u32),
}

fn term_to_core(t: Term) -> syn::Result<CoreTerm> {
    match t {
        Term::Final(TermFinal { term, .. }) => Ok(CoreTerm::Final(Box::new(term_to_core(*term)?))),
        Term::Model(TermModel { term, .. }) => Ok(CoreTerm::Model(Box::new(term_to_core(*term)?))),
        Term::Call(TermCall {
            func,
            paren_token: _,
            args,
        }) => {
            let Term::Path(TermPath { inner }) = *func else {
                return Err(Error::new(func.span(), "Expected path"));
            };
            Ok(CoreTerm::Call(
                inner,
                args.into_iter()
                    .map(term_to_core)
                    .collect::<syn::Result<_>>()?,
            ))
        }
        Term::MethodCall(TermMethodCall {
            receiver,
            dot_token,
            method,
            paren_token,
            args,
            turbofish,
        }) => Ok(CoreTerm::MethodCall(
            Box::new(term_to_core(*receiver)?),
            method,
            args.into_iter()
                .map(term_to_core)
                .collect::<syn::Result<_>>()?,
        )),
        Term::Binary(TermBinary { left, op, right }) => Ok(CoreTerm::BinOp(
            Box::new(term_to_core(*left)?),
            op,
            Box::new(term_to_core(*right)?),
        )),
        Term::Unary(TermUnary { op, expr }) => {
            Ok(CoreTerm::UnOp(op, Box::new(term_to_core(*expr)?)))
        }
        Term::Block(TermBlock { label, block }) => block_to_core(block),
        Term::Match(TermMatch {
            expr,
            arms,
            match_token,
            brace_token,
        }) => {
            let expr = term_to_core(*expr)?;
            let arms = arms
                .into_iter()
                .map(
                    |TermArm {
                         pat,
                         guard,
                         fat_arrow_token,
                         body,
                         comma,
                     }| Ok((pat, Box::new(term_to_core(*body)?))),
                )
                .collect::<syn::Result<_>>()?;
            Ok(CoreTerm::Match(Box::new(expr), arms))
        }
        _ => Err(Error::new(t.span(), "Unsupported term")),
    }
}

fn block_to_core(b: TBlock) -> syn::Result<CoreTerm> {
    let span = b.span();
    let TBlock {
        mut stmts,
        brace_token,
    } = b;
    let Some(TermStmt::Expr(e)) = stmts.pop() else {
        return Err(Error::new(span, "Block must end with an expression"));
    };

    stmts
        .into_iter()
        .try_rfold(term_to_core(e)?, |acc, stmt| match stmt {
            TermStmt::Local(TLocal {
                let_token,
                pat,
                init: Some(init),
                semi_token,
            }) => Ok(CoreTerm::Let(
                pat,
                Box::new(term_to_core(*init.1)?),
                Box::new(acc),
            )),
            TermStmt::Item(_) => Err(Error::new(stmt.span(), "Unsupported term")),
            TermStmt::Expr(_) => Err(Error::new(stmt.span(), "Unexpected expression in block")),
            TermStmt::Semi(_, _) => Err(Error::new(stmt.span(), "Unexpected expression in block")),
            _ => todo!(),
        })
}

fn remove_bound_vars(p: &Pat, subst: &mut Subst) {
    match p {
        Pat::Ident(PatIdent { ident, .. }) => {
            subst.bindings.remove(&VarKind::Source(ident.clone()));
        }
        Pat::Path(PatPath { qself, path, .. }) => {
            todo!()
        }
        Pat::Struct(PatStruct {
            qself,
            path,
            fields,
            ..
        }) => {
            fields
                .iter()
                .for_each(|p| remove_bound_vars(&*p.pat, subst));
        }
        Pat::Tuple(PatTuple { elems, .. }) => {
            elems.iter().for_each(|p| remove_bound_vars(p, subst));
        }
        Pat::TupleStruct(PatTupleStruct {
            qself, path, elems, ..
        }) => {
            elems.iter().for_each(|p| remove_bound_vars(p, subst));
        }
        Pat::Wild(PatWild { .. }) => {}
        _ => todo!(),
    }
}

impl CoreTerm {
    fn subst(&mut self, subst: &mut Subst) {
        match self {
            CoreTerm::Call(_, args) => {
                args.iter_mut().for_each(|a| a.subst(subst));
            }
            CoreTerm::MethodCall(receiver, _, args) => {
                receiver.subst(subst);
                args.iter_mut().for_each(|a| a.subst(subst));
            }
            CoreTerm::BinOp(l, _, r) => {
                l.subst(subst);
                r.subst(subst);
            }
            CoreTerm::UnOp(_, t) => {
                t.subst(subst);
            }
            CoreTerm::Final(t) => {
                t.subst(subst);
            }
            CoreTerm::Model(t) => {
                t.subst(subst);
            }
            CoreTerm::Let(_, t, body) => {
                t.subst(subst);
                body.subst(subst);
            }
            CoreTerm::Match(expr, arms) => {
                expr.subst(subst);
                // TODO: Remove bound variables from the substitution.
                arms.iter_mut().for_each(|(pat, body)| {
                    let mut subst = subst.clone();
                    remove_bound_vars(pat, &mut subst);
                    body.subst(&mut subst)
                });
            }
            CoreTerm::Constructor(ConstructorKind::Tuple(elems)) => {
                elems.iter_mut().for_each(|e| e.subst(subst));
            }
            CoreTerm::Constructor(ConstructorKind::Struct { fields, .. }) => {
                fields.iter_mut().for_each(|(_, e)| e.subst(subst));
            }
            CoreTerm::Constructor(ConstructorKind::TupleStruct { elems, .. }) => {
                elems.iter_mut().for_each(|e| e.subst(subst));
            }
            CoreTerm::Var(v) => {
                if let Some(new) = subst.bindings.get(v) {
                    *self = CoreTerm::Var(new.clone());
                }
            }
        }
    }
}

#[derive(Clone, Default)]
struct Context {
    asserts: Vec<CoreTerm>,
    bound_vars: u32,
}

fn build_existential_pattern(
    pat: Pat,
    next_free: &mut u32,
    subst: &mut Vec<(VarKind, VarKind)>,
) -> CoreTerm {
    match pat {
        Pat::Ident(PatIdent { ident, .. }) => {
            let var = VarKind::DeBruijn(*next_free);
            *next_free += 1;
            subst.push((VarKind::Source(ident.clone()), var.clone()));
            CoreTerm::Var(var)
        }
        Pat::Path(PatPath { qself, path, .. }) => {
            todo!()
        }
        Pat::Struct(PatStruct {
            qself,
            path,
            fields,
            ..
        }) => {
            let fields = fields
                .into_iter()
                .map(|e| {
                    (
                        e.member,
                        build_existential_pattern(*e.pat, next_free, subst),
                    )
                })
                .collect();

            CoreTerm::Constructor(ConstructorKind::Struct {
                fields,
                qself,
                path,
            })
        }
        Pat::Tuple(PatTuple { elems, .. }) => {
            let elems = elems
                .into_iter()
                .map(|e| build_existential_pattern(e, next_free, subst))
                .collect();

            CoreTerm::Constructor(ConstructorKind::Tuple(elems))
        }
        Pat::TupleStruct(PatTupleStruct {
            qself, path, elems, ..
        }) => {
            let elems = elems
                .into_iter()
                .map(|e| build_existential_pattern(e, next_free, subst))
                .collect();

            CoreTerm::Constructor(ConstructorKind::TupleStruct { elems, qself, path })
        }
        Pat::Wild(PatWild { .. }) => {
            let var = VarKind::DeBruijn(*next_free);
            *next_free += 1;
            CoreTerm::Var(var)
        }
        _ => todo!(),
    }
}

impl Context {
    fn extend(&mut self, mut o: Self) -> Subst {
        let shift = (0..o.bound_vars)
            .map(|i| (VarKind::DeBruijn(i), VarKind::DeBruijn(i + self.bound_vars)));
        let shift_subst = Subst {
            bindings: shift.collect(),
        };
        o.asserts
            .iter_mut()
            .for_each(|t| t.subst(&mut shift_subst.clone()));

        self.asserts.extend(o.asserts);
        shift_subst
    }

    fn merge(mut self, o: Self) -> Self {
        self.asserts.extend(o.asserts);
        self
    }

    fn bind(&mut self, pat: Pat, term: CoreTerm, next_fresh: &mut u32) -> Subst {
        // let old_bound_vars = self.bound_vars;
        let mut subst = Vec::new();
        let pattern = build_existential_pattern(pat, next_fresh, &mut subst);
        let subst = Subst {
            bindings: subst.into_iter().collect(),
        };
        self.asserts.push(CoreTerm::BinOp(
            Box::new(term.clone()),
            BinOp::Eq(Default::default()),
            Box::new(pattern),
        ));
        subst
    }
}

#[derive(Default, Clone)]
struct Subst {
    bindings: HashMap<VarKind, VarKind>,
}

impl Subst {
    fn extend(&mut self, o: Subst) {
        todo!()
    }
}

macro_rules! mdo {
    // return
    (return $r:expr ;) => {
      vec![$r]
    };

    // let-binding
    (let $p:pat = $e:expr ; $($r:tt)*) => {{
      let $p = $e;
      mdo!($($r)*)
    }};

    // bind
    (($($binding:pat),*) <- $x:expr ; $($r:tt)*) => {
      $x.into_iter().flat_map(|($($binding),*)| { mdo!($($r)*) }).collect::<Vec<_>>()
    };

    // pure
    ($a:expr) => {
      $a
    }
  }

/// Eliminates matches by replacing them with existential quantifications.
/// The result is a pair of a one-hole context and the term which plugs it.
fn eliminate_match(t: CoreTerm, next_fresh: &mut u32) -> Vec<(Context, CoreTerm)> {
    match t {
        CoreTerm::Call(path, args) => {
            let args: Vec<_> = args
                .into_iter()
                .map(|a| eliminate_match(a, next_fresh))
                .collect();
            args.into_iter()
                .multi_cartesian_product()
                .map(|args| {
                    let (ctxs, args): (Vec<_>, _) = args.into_iter().unzip();
                    let (ctx, mut subst) = ctxs.into_iter().fold(
                        (Context::default(), Subst::default()),
                        |(mut ctx, mut subst), new| {
                            let s = ctx.extend(new);
                            subst.extend(s);
                            (ctx, subst)
                        },
                    );
                    let mut t = CoreTerm::Call(path.clone(), args);
                    t.subst(&mut subst);
                    (ctx, t)
                })
                .collect()
        }
        CoreTerm::BinOp(l, op, r) => mdo! {
            (ctx_l, l) <- eliminate_match(*l, next_fresh) ;
            (ctx_r, r) <- eliminate_match(*r.clone(), next_fresh) ;
            return (ctx_l.clone().merge(ctx_r), CoreTerm::BinOp(Box::new(l.clone()), op, Box::new(r))) ;
        },
        CoreTerm::UnOp(op, t) => mdo! {
            (ctx, t) <- eliminate_match(*t, next_fresh) ;
            return (ctx, CoreTerm::UnOp(op, Box::new(t))) ;
        },
        CoreTerm::Final(t) => mdo! {
            (ctx, t) <- eliminate_match(*t, next_fresh) ;
            return (ctx, CoreTerm::Final(Box::new(t))) ;
        },
        CoreTerm::Model(t) => mdo! {
            (ctx, t) <- eliminate_match(*t, next_fresh) ;
            return (ctx, CoreTerm::Model(Box::new(t))) ;
        },
        CoreTerm::Let(pat, t, body) => mdo! {
            (ctx_t, t) <- eliminate_match(*t, next_fresh) ;
            (ctx_body, body) <- eliminate_match((*body).clone(), next_fresh) ;
            return (ctx_t.clone().merge(ctx_body), CoreTerm::Let(pat.clone(), Box::new(t.clone()), Box::new(body))) ;
        },
        CoreTerm::Match(expr, arms) => mdo! {
            (ctx_e, expr) <- eliminate_match(*expr, next_fresh);
            (pat, body) <- arms.clone();

            // let (mut ctx_body, mut body) = todo!();
            (mut ctx_body, mut body) <- eliminate_match(*body, next_fresh);
            let mut subst = ctx_body.extend(ctx_e.clone());
            let () = subst.extend(ctx_body.bind(pat.clone(), expr.clone(), next_fresh));
            let () = body.subst(&mut subst);
            return vec![(ctx_body, body)]

        },
        _ => todo!(),
    }
}
