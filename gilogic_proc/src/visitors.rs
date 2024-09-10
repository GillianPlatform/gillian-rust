// Utilities to expand our macros when parsing.
// Long term, we should rework everything as one big macro, with good semantics.
// Until then, we want a proof of concept that things can work.

use quote::quote;
use syn::{
    parse_quote,
    visit::{self, Visit},
    visit_mut::{self, VisitMut},
    Expr, ExprMacro, Ident, Macro,
};

use crate::gilogic_syn::Assertion;

pub trait AssertMutator {
    fn mutate_assert(&mut self, asrt: &mut Assertion);
}

pub struct AssertMutatorImpl<F: AssertMutator>(F);

impl<F> From<F> for AssertMutatorImpl<F>
where
    F: AssertMutator,
{
    fn from(f: F) -> Self {
        Self(f)
    }
}

impl<M: AssertMutator> AssertMutatorImpl<M> {
    pub fn into_inner(self) -> M {
        self.0
    }
}

impl<M: AssertMutator> VisitMut for AssertMutatorImpl<M> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        if let Expr::Macro(ExprMacro {
            mac: Macro { path, tokens, .. },
            ..
        }) = expr
        {
            match path.segments.iter().last() {
                Some(segment) => {
                    if segment.ident == "assertion" {
                        let mut assertion = syn::parse::<Assertion>(tokens.clone().into())
                            .expect("Failed to expand inner macro");
                        self.0.mutate_assert(&mut assertion);
                        *expr = syn::parse2::<Expr>(quote! { assertion!(#assertion) }).unwrap();
                    }
                }
                None => panic!("Empty path in macro"),
            }
            visit_mut::visit_expr_mut(self, expr);
        }
    }

    fn visit_stmt_macro_mut(&mut self, i: &mut syn::StmtMacro) {
        let Macro { path, tokens, .. } = &mut i.mac;

        match path.segments.iter().last() {
            Some(segment) => {
                if segment.ident == "assertion" {
                    let mut assertion = syn::parse::<Assertion>(tokens.clone().into())
                        .expect("Failed to expand inner macro");
                    self.0.mutate_assert(&mut assertion);
                    i.mac = parse_quote! { assertion!(#assertion) };
                }
            }
            None => panic!("Empty path in macro"),
        };
        visit_mut::visit_stmt_macro_mut(self, i);
    }
}

pub struct IdentSubst(pub Vec<(String, String)>);

impl VisitMut for IdentSubst {
    fn visit_ident_mut(&mut self, ident: &mut Ident) {
        for (k, v) in self.0.iter() {
            if ident == k.as_str() {
                *ident = Ident::new(v, ident.span());
                return;
            }
        }
    }
}

pub trait AssertVisitor {
    fn visit_assert(&mut self, asrt: &Assertion);
}

pub struct AssertVisitorImpl<F: AssertVisitor>(F);

impl<F> From<F> for AssertVisitorImpl<F>
where
    F: AssertVisitor,
{
    fn from(f: F) -> Self {
        Self(f)
    }
}

impl<M: AssertVisitor> AssertVisitorImpl<M> {
    pub fn into_inner(self) -> M {
        self.0
    }
}

impl<'ast, M: AssertVisitor> Visit<'ast> for AssertVisitorImpl<M> {
    fn visit_expr(&mut self, expr: &'ast Expr) {
        if let Expr::Macro(ExprMacro {
            mac: Macro { path, tokens, .. },
            ..
        }) = expr
        {
            match path.segments.iter().last() {
                Some(segment) => {
                    if segment.ident == "assertion" {
                        let assertion = syn::parse::<Assertion>(tokens.clone().into())
                            .expect("Failed to expand inner macro");
                        self.0.visit_assert(&assertion);
                    }
                }
                None => panic!("Empty path in macro"),
            }
            visit::visit_expr(self, expr);
        }
    }
}
