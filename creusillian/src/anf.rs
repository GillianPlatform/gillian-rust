use std::collections::HashMap;

use itertools::Itertools;
use pearlite_syn::*;
use syn::{spanned::Spanned, BinOp, Error, ExprPath, Ident, Pat, PatIdent, PatTuple, PatStruct, PatPath, PatTupleStruct, PatWild, Path, UnOp};

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
#[derive(Clone)]
enum ConstructorKind {
    Tuple(Vec<CoreTerm>),
    Struct(),
    TupleStruct(),
}
#[derive(Clone)]
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
            paren_token,
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
            _ => todo!(),
            TermStmt::Item(_) => Err(Error::new(stmt.span(), "Unsupported term")),
            TermStmt::Expr(_) => Err(Error::new(stmt.span(), "Unexpected expression in block")),
            TermStmt::Semi(_, _) => Err(Error::new(stmt.span(), "Unexpected expression in block")),
        })
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
    ($binding:pat <- $x:expr ; $($r:tt)*) => {
      $x.into_iter().flat_map(move |$binding| { mdo!($($r)*) }).collect::<Vec<_>>()
    };

    // pure
    ($a:expr) => {
      $a
    }
  }

#[derive(Clone, Default)]
struct Context { asserts: Vec<CoreTerm>, bound_vars: u32 }

fn build_existential_pattern(pat: Pat, next_free: &mut u32, subst: &mut Vec<(Ident, u32)>) -> CoreTerm {
    match pat {
        Pat::Ident(PatIdent { ident, .. }) => {
            let var = VarKind::DeBruijn(*next_free);
            *next_free += 1;
            subst.push((ident.clone(), var));
            CoreTerm::Var(var)
        },
        Pat::Path(PatPath { qself, path, .. }) => {
            todo!()
        },
        Pat::Struct(PathStruct{}) => todo!(),
        Pat::Tuple(PatTuple{ elems, ..}) => {

        },
        Pat::TupleStruct(PatTupleStruct{ qself, path, elems, .. }) => {

        },
        Pat::Wild(PatWild{ .. }) => {
            let var = VarKind::DeBruijn(*next_free);
            *next_free += 1;
            CoreTerm::Var(var)
        },
        _ => todo!(),
    }
} 

impl Context {
    fn extend(&mut self, o: Self) -> Subst {
        let shift = (0..o.bound_vars).map(|i| (VarKind::DeBruijn(i), VarKind::DeBruijn(i + self.bound_vars)));
        let shift_subst = Subst { bindings: shift_substs.collect() };
        self.asserts.extend(o.asserts.into_iter().map(|t| t.subst(shift_subst.clone())));
        shift_subst
    }

    fn bind(&mut self, pat: Pat, term: CoreTerm) -> Subst {
        let old_bound_vars = self.bound_vars;
        let mut subst = Vec::new();
        let pattern = build_existential_pattern(pat, &mut self.bound_vars, &mut subst);
        let subst = Subst { bindings: subst.into_iter().map(|(nm, tgt)| (VarKind::Source(nm), VarKind::DeBruijn(tgt))).collect() };
        self.asserts.push(CoreTerm::BinOp(Box::new(term.clone()), BinOp::Eq(Default::default()), Box::new(pattern)));
        subst
    }
}

#[derive(Default)]
struct Subst {
    bindings: HashMap<VarKind, VarKind>,
}

impl Subst {
    fn extend(&mut self, o: Subst) {
        todo!()
    }
}

/// Eliminates matches by replacing them with existential quantifications.
/// The result is a pair of a one-hole context and the term which plugs it.
fn eliminate_match(t: CoreTerm) -> Vec<(Context, CoreTerm)> {
    match t {
        CoreTerm::Call(path, args) => {
            let args: Vec<_> = args.into_iter().map(|a| eliminate_match(a)).collect();
            args.into_iter()
                .multi_cartesian_product()
                .map(|args| {
                    let (ctxs, args) : (Vec<_>, _) = args.into_iter().unzip();
                    (
                        ctxs.into_iter().fold((Context::default(), Subst::default()), |(mut ctx, mut subst), new| {
                            let s = ctx.extend(new);
                            subst.extend(s);
                            (ctx, subst)
                        }),

                        CoreTerm::Call(path.clone(), args),
                    )
                })
                .collect()
        } , 
        CoreTerm::BinOp(l, op, r) => mdo!{
            (ctx_l, l) <- eliminate_match(*l) ;
            (ctx_r, r) <- eliminate_match(*r) ;
            return (ctx_l.merge(ctx_r), CoreTerm::BinOp(Box::new(l), op, Box::new(r))) ;
        },
        CoreTerm::UnOp(op, t) => mdo! {
            (ctx, t) <- eliminate_match(*t) ;
            return (ctx, CoreTerm::UnOp(op, Box::new(t))) ;
        },
        CoreTerm::Final(t) => mdo! {
            (ctx, t) <- eliminate_match(*t) ;
            return (ctx, CoreTerm::Final(Box::new(t))) ;
        },
        CoreTerm::Model(t) => mdo! {
            (ctx, t) <- eliminate_match(*t) ;
            return (ctx, CoreTerm::Model(Box::new(t))) ;
        },
        CoreTerm::Let(pat, t, body) => mdo! {
            (ctx_t, t) <- eliminate_match(*t) ;
            (ctx_body, body) <- eliminate_match(*body) ;
            return (ctx_t.merge(ctx_body), CoreTerm::Let(pat, Box::new(t), Box::new(body))) ;
        },
        CoreTerm::Match(expr, arms) => mdo!{
           (ctx_e, expr) <- eliminate_match(*expr);
           return arms.into_iter().map(|(pat, body)| {
            mdo! {
                (mut ctx_body, body) <- eliminate_match(*body);
                let subst = ctx_body.extend(ctx_e);
                let () = subst.extend(ctx.bind(pat, expr.clone()));
                
                return (ctx, body.subst(subst))
              }
            
            }).collect()
           },
        _ => todo!(),
    }
}
