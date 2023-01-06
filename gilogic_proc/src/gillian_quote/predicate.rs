use quote::{quote, ToTokens};
use syn::Stmt;

use crate::gillian_syn::predicate::{PredParam, PredParamS, Predicate};

impl ToTokens for PredParamS {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let name = &self.name;
        let ty = &self.ty;
        let colon = &self.colon_token;
        tokens.extend(quote!(#name #colon #ty))
    }
}

impl ToTokens for PredParam {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            Self::Receiver(self_token) => self_token.to_tokens(tokens),
            Self::S(s) => s.to_tokens(tokens),
        }
    }
}

fn gather_ins(args: &syn::punctuated::Punctuated<PredParam, syn::token::Comma>) -> String {
    let v: Vec<String> = args
        .iter()
        .enumerate()
        .filter_map(|(i, p)| if p.is_in() { Some(i.to_string()) } else { None })
        .collect();
    v.join(",")
}

impl ToTokens for Predicate {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let ins = gather_ins(self.args());
        match self {
            Self::Abstract {
                name,
                args,
                generics,
            } => tokens.extend(quote! {
              #[gillian::decl::abstract_predicate]
              #[gillian::decl::pred_ins=#ins]
              fn #name #generics (#args) {
                unreachable!()
              }
            }),
            Self::Concrete {
                name,
                generics,
                args,
                body,
            } => {
                let stmts: Vec<_> = body
                    .stmts
                    .iter()
                    .map(|stmt| match stmt {
                        Stmt::Semi(e, _) => Stmt::Expr(e.clone()),
                        _ => stmt.clone(),
                    })
                    .collect();
                let brace_token = body.brace_token;
                tokens.extend(quote! {
                  #[cfg(gillian)]
                  #[gillian::decl::predicate]
                  #[gillian::decl::pred_ins=#ins]
                  fn #name #generics (#args) -> ::gilogic::RustAssertion
                });
                brace_token.surround(tokens, |tokens| {
                    tokens.extend(quote!(::gilogic::__stubs::defs([#(#stmts),*])));
                })
            }
        }
    }
}
