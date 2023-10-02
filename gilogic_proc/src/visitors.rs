// Utilities to expand our macros when parsing.
// Long term, we should rework everything as one big macro, with good semantics.
// Until then, we want a proof of concept that things can work.

use quote::quote;
use syn::{
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
