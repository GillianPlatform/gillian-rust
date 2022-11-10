use quote::{quote_spanned, ToTokens};
use syn::spanned::Spanned;

use crate::gillian_syn::formula::Formula;

impl ToTokens for Formula {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            Self::Eq { left, right, tok } => {
                let span = tok.span();
                tokens.extend(quote_spanned!(span=>
                    ::gilogic::__stubs::equal(#left, #right)
                ))
            }
        }
    }
}
