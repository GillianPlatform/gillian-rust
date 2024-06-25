use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::{spanned::Spanned, BinOp, Error, Stmt};

use crate::{extract_lemmas::ExtractLemma, gilogic_syn::*};

impl Formula {
    fn encode_inner(inner: &Term) -> syn::Result<TokenStream> {
        let mut tokens = TokenStream::new();
        eprintln!("{inner:?}");
        match inner {
            Term::Binary(TermBinary { left, op, right }) => match op {
                BinOp::Eq(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                      gilogic::__stubs::equal(#left, #right)
                    ));
                }
                BinOp::Le(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                      gilogic::__stubs::less_eq(#left, #right)
                    ));
                }
                BinOp::Lt(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                      gilogic::__stubs::less(#left, #right)
                    ));
                }
                BinOp::Gt(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                      gilogic::__stubs::less(#right, #left)
                    ));
                }
                BinOp::Ge(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                        gilogic::__stubs::less(#right, #left)
                    ));
                }
                BinOp::And(tok) => {
                    let span = tok.span();
                    let left = Self::encode_inner(left)?;
                    let right = Self::encode_inner(right)?;
                    tokens.extend(quote_spanned!(span=>
                        gilogic::__stubs::and(#left, #right)
                    ));
                }
                BinOp::Or(tok) => {
                    let span = tok.span();
                    let left = Self::encode_inner(left)?;
                    let right = Self::encode_inner(right)?;
                    tokens.extend(quote_spanned!(span=>
                        gilogic::__stubs::or(#left, #right)
                    ));
                }
                BinOp::Ne(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                        gilogic::__stubs::not_equal(#left, #right)
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
            Term::Forall(TermForall {
                forall_token: _,
                lt_token: _,
                args,
                gt_token: _,
                term,
            }) => {
                let mut ts = Self::encode_inner(term)?;
                for arg in args {
                    ts = quote! {
                        gilogic::__stubs::forall(
                            #[gillian::no_translate]
                            |#arg| { #ts }
                        )
                    }
                }
                tokens.extend(ts)
            }
            Term::Exists(TermExists {
                exists_token: _,
                lt_token: _,
                args,
                gt_token: _,
                term,
            }) => {
                let mut ts = Self::encode_inner(term)?;
                for arg in args {
                    ts = quote! {
                        gilogic::__stubs::exists(
                            #[gillian::no_translate]
                            (|#arg| #ts)
                        )
                    }
                }
                tokens.extend(ts)
            }
            Term::Impl(TermImpl {
                hyp,
                eqeq_token: _,
                gt_token: _,
                cons,
            }) => {
                let span = inner.span();
                let hyp = Self::encode_inner(hyp)?;
                let cons = Self::encode_inner(cons)?;
                tokens.extend(quote_spanned! {span=>
                    gilogic::__stubs::implication(#hyp, #cons)
                });
            }
            Term::Path(p) => tokens.extend(quote!(
              gilogic::__stubs::equal(#p, true)
            )),
            Term::Lit(l) => tokens.extend(quote! { #l }),
            e => {
                return Err(Error::new(
                    inner.span(),
                    format!("Expression is not a supported formula {e:?}"),
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
                Ok(quote_spanned!(span=> gilogic::__stubs::emp()))
            }
            Self::PointsTo(AsrtPointsTo { left, right, .. }) => {
                Ok(quote!(gilogic::__stubs::PointsTo::points_to(#left, #right)))
            }
            Self::Pure(formula) => {
                let formula = formula.encode()?;
                Ok(quote!(gilogic::__stubs::pure(#formula)))
            }
            Self::Observation(obs) => {
                let observation = obs.encode()?;
                Ok(quote!(gilogic::__stubs::observation(#observation)))
            }
            Self::PredCall(call) => Ok(call.to_token_stream()),
        }
    }
}

impl SpecEnsures {
    pub fn encode(&self) -> syn::Result<TokenStream> {
        let def = {
            let mut fragments = self.postcond.iter();
            let first = fragments.next().unwrap().encode();
            fragments.fold(first, |acc, fragment| {
                let acc = acc?;
                let right = fragment.encode()?;
                Ok(quote!(gilogic::__stubs::star(#acc, #right)))
            })?
        };

        let rvars = self.rvars.iter();
        let postcond_tokens = quote!({
            gilogic::__stubs::instantiate_lvars(#[gillian::no_translate] |#(#rvars),*| {
                #def
            })
        });

        Ok(postcond_tokens)
    }
}

impl Specification {
    pub fn encode(&self) -> syn::Result<TokenStream> {
        // Temporary for easier compatibility with existing code;

        let precond_tokens = {
            let mut fragments = self.precond.iter();
            let first = fragments.next().unwrap().encode();
            fragments.fold(first, |acc, fragment| {
                let acc = acc?;
                let right = fragment.encode()?;
                Ok(quote!(gilogic::__stubs::star(#acc, #right)))
            })?
        };

        let postcond_tokens = self
            .postconds
            .iter()
            .map(|a| a.encode())
            .collect::<syn::Result<Vec<_>>>()?;

        let lvars = self.lvars.iter();

        Ok(quote! {
            unsafe { gilogic::__stubs::instantiate_lvars(#[gillian::no_translate] |#(#lvars),*| {
                gilogic::__stubs::spec(#precond_tokens, [#(#postcond_tokens),*])
            }) }
        })
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
                Ok(quote!(gilogic::__stubs::star(#acc, #right)))
            })?
        };
        tokens.extend(quote!({
            unsafe {
                gilogic::__stubs::instantiate_lvars(#[gillian::no_translate] |#(#lvars),*| {
                    #def
                })
            }
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
              fn #name #generics (#args) -> gilogic::RustAssertion {
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
                  fn #name #generics (#args) -> gilogic::RustAssertion
                });
                brace_token.surround(tokens, |tokens| {
                    tokens.extend(quote!(gilogic::__stubs::defs([#(#stmts),*])));
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
                #[gillian::decl::lemma]
                #[gillian::lemma::trusted]
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

impl ToTokens for frozen_borrow::FreezeMutRefOwn {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let own_impl = &self.own_impl;
        let predicate = &self.predicate;
        let generics = &predicate.generics;
        let own_impl_ty = &self.own_impl.self_ty;
        let name = &predicate.name;
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
            #[allow(non_snake_case)]
            #[specification(
                requires { REFERENCE.own() }
                exists #(#additional_args),*.
                ensures { #name(REFERENCE, #(#additional_args),*) }
            )]
            fn #lemma_name #generics (REFERENCE: &mut #own_impl_ty);

            #[gillian::borrow]
            // #lifetimes
            #predicate

            #own_impl
        })
    }
}

impl ToTokens for frozen_borrow_pcy::FreezeMutRefOwn {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let own_impl = &self.own_impl;
        let predicate = &self.predicate;
        let generics = &predicate.generics;
        let inner_predicate = &self.inner_predicate;

        let own_impl_ty = &self.own_impl.self_ty;
        let additional_args: Vec<_> = predicate
            .args
            .iter()
            .skip(predicate.args.len() - self.args.frozen_variables.len())
            .map(|x| match x {
                PredParam::Receiver(..) => {
                    unreachable!()
                }
                PredParam::S(s) => &s.name,
            })
            .collect();
        let lemma_name = &self.args.lemma_name;
        let outer_name = &predicate.name;

        tokens.extend(quote! {

            #[lemma]
            #[specification(
                forall MODEL: <&mut #own_impl_ty as gilogic::prophecies::Ownable>::RepresentationTy.
                requires { REFERENCE.own(MODEL) }
                exists #(#additional_args),*.
                ensures { #outer_name(REFERENCE, MODEL, #(#additional_args),*) }
            )]
            fn #lemma_name #generics (REFERENCE: &mut #own_impl_ty);

            #[gillian::borrow]
            #inner_predicate

            #predicate

            #own_impl
        })
    }
}

impl ToTokens for ExtractLemma {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let lemma = &self.0;

        quote! {
            #[gillian::extract_lemma]
            #[allow(unused_variables)]
            #[allow(dead_code)]
            #lemma
        }
        .to_tokens(tokens);
    }
}
