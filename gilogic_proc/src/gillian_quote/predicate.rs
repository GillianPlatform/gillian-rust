use quote::{quote, ToTokens};

use crate::gillian_syn::predicate::{ParamMode, PredParam, Predicate};

impl ToTokens for PredParam {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let name = &self.name;
        let ty = &self.ty;
        let colon = &self.colon_token;
        match self.mode {
            ParamMode::In => tokens.extend(quote!(#name #colon ::gilogic::__stubs::In<#ty>)),
            ParamMode::Out => tokens.extend(quote!(#name #colon #ty)),
        }
    }
}

impl ToTokens for Predicate {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            Self::Abstract { name, args } => tokens.extend(quote! {
              #[gillian::decl::abstract_predicate]
              fn #name(#args) {
                unreachable!()
              }
            }),
            Self::Concrete { name, args, body } => panic!("bite"),
        }
    }
}
