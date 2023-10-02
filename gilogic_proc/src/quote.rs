use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::{spanned::Spanned, BinOp, Error, Signature, Stmt};

use crate::gilogic_syn::*;

impl Formula {
    fn encode_inner(inner: &Term) -> syn::Result<TokenStream> {
        let mut tokens = TokenStream::new();
        match inner {
            Term::Binary(TermBinary { left, op, right }) => match op {
                BinOp::Eq(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                      ::gilogic::__stubs::equal(#left, #right)
                    ));
                }
                BinOp::Le(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                      ::gilogic::__stubs::less_eq(#left, #right)
                    ));
                }
                BinOp::Lt(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                      ::gilogic::__stubs::less(#left, #right)
                    ));
                }
                _ => {
                    return Err(Error::new(
                        op.span(),
                        "Unsupported binary operator for formula",
                    ))
                }
            },
            Term::Paren(TermParen {
                paren_token: _,
                expr,
            }) => {
                let inner = Self::encode_inner(expr)?;
                tokens.extend(inner);
            }
            _ => {
                return Err(Error::new(
                    inner.span(),
                    "Expression is not a supported formula",
                ))
            }
        }
        Ok(tokens)
    }

    pub fn encode(&self) -> syn::Result<TokenStream> {
        Self::encode_inner(&self.inner)
    }
}

impl Observation {
    fn encode_inner(inner: &Term) -> syn::Result<TokenStream> {
        Formula::encode_inner(inner)
    }

    pub fn encode(&self) -> syn::Result<TokenStream> {
        Self::encode_inner(&self.inner)
    }
}

impl AsrtFragment {
    pub fn encode(&self) -> syn::Result<TokenStream> {
        match self {
            Self::Emp(emp) => {
                let span = emp.span();
                Ok(quote_spanned!(span=> ::gilogic::__stubs::emp()))
            }
            Self::PointsTo(AsrtPointsTo { left, right, .. }) => {
                Ok(quote!(::gilogic::__stubs::PointsTo::points_to(#left, #right)))
            }
            Self::Pure(formula) => {
                let formula = formula.encode()?;
                Ok(quote!(::gilogic::__stubs::pure(#formula)))
            }
            Self::Observation(obs) => {
                let observation = obs.encode()?;
                Ok(quote!(::gilogic::__stubs::observation(#observation)))
            }
            Self::PredCall(call) => Ok(call.to_token_stream()),
            Self::__Nonexhaustive => todo!(),
        }
    }
}

impl Assertion {
    pub fn encode(&self) -> syn::Result<TokenStream> {
        let mut tokens = TokenStream::new();
        let lvars = self.lvars.iter();
        // Assertion is guaranteed to be a non-empty list of fragments
        let def = {
            let mut fragments = self.def.iter();
            let first = fragments.next().unwrap().encode();
            fragments.fold(first, |acc, fragment| {
                let acc = acc?;
                let right = fragment.encode()?;
                Ok(quote!(::gilogic::__stubs::star(#acc, #right)))
            })?
        };
        tokens.extend(quote!({
            #(let #lvars = ::gilogic::__stubs::InstantiateLVar::instantiate_lvar(); )*
            #def
        }));
        Ok(tokens)
    }
}

impl ToTokens for PredParamS {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let name = &self.name;
        let ty = &self.ty;
        let colon = &self.colon_token;
        tokens.extend(quote!(#name #colon #ty))
    }
}

impl ToTokens for PredParam {
    fn to_tokens(&self, tokens: &mut TokenStream) {
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
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ins = gather_ins(&self.args);
        let Predicate {
            name,
            body,
            generics,
            args,
            attributes,
        } = &self;
        match body {
            None => tokens.extend(quote! {
              #[cfg(gillian)]
              #[gillian::decl::abstract_predicate]
              #[gillian::decl::pred_ins=#ins]
              #(#attributes)*
              fn #name #generics (#args) -> ::gilogic::RustAssertion {
                unreachable!()
              }
            }),
            Some(body) => {
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
                  #(#attributes)*
                  fn #name #generics (#args) -> ::gilogic::RustAssertion
                });
                brace_token.surround(tokens, |tokens| {
                    tokens.extend(quote!(::gilogic::__stubs::defs([#(#stmts),*])));
                })
            }
        }
    }
}

impl ToTokens for Lemma {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Lemma {
            attributes,
            sig,
            body,
        } = self;
        match body {
            None => tokens.extend(quote! {
                #[cfg(gillian)]
                #(#attributes)*
                #[gillian::lemma::trusted]
                #[gillian::decl::lemma]
                #sig {
                    unreachable!()
                }
            }),
            Some(body) => tokens.extend(quote! {
                #[cfg(gillian)]
                #(#attributes)*
                #[gillian::decl::lemma]
                #[gillian::lemma::trusted]
                #sig #body
            }),
        }
    }
}

impl ToTokens for FreezeMutRefOwn {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let own_impl = &self.own_impl;
        let predicate = &self.predicate;
        let generics = &predicate.generics;
        let own_impl_ty = &self.own_impl.self_ty;
        let name = &predicate.name;
        let sig = {
            let args = &predicate.args;
            let tokens = quote!(fn #name #generics (#args));
            syn::parse2::<Signature>(tokens).unwrap()
        };
        let lifetimes = super::lifetime_hack::generic_lifetimes_attr(&sig);

        // Then we generate the corresponding lemma.

        let additional_args: Vec<_> = predicate
            .args
            .iter()
            .skip(predicate.args.len() - self.args.frozen_variables.len())
            .map(|x| match x {
                PredParam::Receiver(..) => unreachable!(),
                PredParam::S(s) => &s.name,
            })
            .collect();
        let lemma_name = &self.args.lemma_name;

        tokens.extend(quote! {

            #[lemma]
            #[requires(REFERENCE.own())]
            #[ensures(|#(#additional_args),*| #name(REFERENCE, #(#additional_args),*))]
            fn #lemma_name #generics (REFERENCE: &mut #own_impl_ty);

            #[gillian::borrow]
            #lifetimes
            #predicate

            #own_impl
        })
    }
}
