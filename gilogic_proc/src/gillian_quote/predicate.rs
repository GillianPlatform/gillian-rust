use quote::{quote, ToTokens, TokenStreamExt};

use crate::gillian_syn::predicate::{ParamMode, PredParam, Predicate};

impl ToTokens for PredParam {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let name = &self.name;
        let ty = &self.ty;
        let colon = &self.colon_token;
        tokens.extend(quote!(#name #colon #ty))
    }
}

fn gather_ins(args: &syn::punctuated::Punctuated<PredParam, syn::token::Comma>) -> String {
    let v: Vec<String> = args
        .iter()
        .enumerate()
        .filter_map(|(i, p)| {
            if let ParamMode::In = p.mode {
                Some(i.to_string())
            } else {
                None
            }
        })
        .collect();
    v.join(",")
}

impl ToTokens for Predicate {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let ins = gather_ins(self.args());
        match self {
            Self::Abstract { name, args } => tokens.extend(quote! {
              #[gillian::decl::abstract_predicate]
              #[gillian::decl::pred_ins=#ins]
              fn #name(#args) {
                unreachable!()
              }
            }),
            Self::Concrete {
                name,
                args,
                body,
                brace_token,
            } => {
                tokens.extend(quote! {
                  #[gillian::decl::predicate]
                  #[gillian::decl::pred_ins=#ins]
                  fn #name(#args)
                });
                brace_token.surround(tokens, |tokens| {
                    tokens.append_all(body);
                    tokens.extend(quote!(;))
                })
            }
        }
    }
}
