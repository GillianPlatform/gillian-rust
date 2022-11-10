use quote::{quote_spanned, ToTokens};
use syn::spanned::Spanned;

use crate::gillian_syn::assertion::{Assertion, SimpleAssertion};

impl ToTokens for SimpleAssertion {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            Self::Emp(span) => {
                let span = *span;
                tokens.extend(quote_spanned!(span=> ::gilogic::__stubs::emp()))
            }
            Self::Pure(form) => {
                let form = form.to_token_stream();
                let span = form.span();
                tokens.extend(quote_spanned!(span=> ::gilogic::__stubs::pure(#form)))
            }
            Self::PointsTo(id, dash, arr_head, exp) => {
                let span = dash
                    .span()
                    .join(arr_head.span())
                    .expect("gilogic can only be used in nightly Rust for now");
                tokens.extend(
                    quote_spanned!(span=> ::gilogic::__stubs::PointsTo::points_to(#id, #exp)),
                )
            }
        }
    }
}

impl ToTokens for Assertion {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            Assertion::Leaf(simple) => simple.to_tokens(tokens),
            Assertion::Star {
                left,
                right,
                star_token,
            } => {
                let span = star_token.span();
                tokens.extend(quote_spanned!(span=> ::gilogic::__stubs::star(#left, #right)))
            }
        }
    }
}
