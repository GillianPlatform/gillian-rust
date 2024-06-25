extern crate proc_macro;
use std::collections::HashMap;

use anf::{term_to_core, CoreTerm};
use itertools::{Either, Itertools};
use pearlite_syn::Term;
use proc_macro::TokenStream as TokenStream_;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
    parse::Parse, punctuated::Punctuated, token::Comma, Attribute, FnArg, Ident, Pat, PatIdent,
    PatType, Receiver, ReturnType, Signature, Visibility,
};

use crate::anf::{core_to_sl, elim_match_form, print_gilsonite, Disjuncts, Subst, VarKind};

mod anf;

struct AttrTrail(Vec<Attribute>, Visibility, Signature, TokenStream);

impl Parse for AttrTrail {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(AttrTrail(
            Attribute::parse_outer(input)?,
            input.parse()?,
            input.parse()?,
            input.parse()?,
        ))
    }
}

impl AttrTrail {
    fn extract_contract(mut self) -> syn::Result<(RawContract, Self)> {
        let (contract, rest): (Vec<_>, _) = self
            .0
            .into_iter()
            .partition(|attr| attr.path().is_ident("requires") || attr.path().is_ident("ensures"));

        self.0 = rest;
        let (pre, post): (Vec<_>, Vec<_>) = contract.into_iter().partition_map(|attr| {
            if attr.path().is_ident("requires") {
                Either::Left(attr)
            } else {
                Either::Right(attr)
            }
        });

        let pre = pre
            .into_iter()
            .map(|a| a.parse_args::<Term>())
            .collect::<syn::Result<Vec<_>>>()?;
        let post = post
            .into_iter()
            .map(|a| a.parse_args::<Term>())
            .collect::<syn::Result<Vec<_>>>()?;

        Ok((
            RawContract(self.2.inputs.clone(), self.2.output.clone(), pre, post),
            self,
        ))
    }
}

// Here we should have one term as a pre and many as a disjunction of posts but that's not what is actually being encoded here.
struct RawContract(Punctuated<FnArg, Comma>, ReturnType, Vec<Term>, Vec<Term>);

impl RawContract {
    fn elaborate(self) -> syn::Result<CoreContract> {
        let pres = self
            .2
            .into_iter()
            .map(term_to_core)
            .collect::<syn::Result<_>>()?;
        let posts = self
            .3
            .into_iter()
            .map(term_to_core)
            .collect::<syn::Result<_>>()?;
        Ok(CoreContract(self.0, self.1, pres, posts))
    }
}

struct CoreContract(
    Punctuated<FnArg, Comma>,
    ReturnType,
    Vec<CoreTerm>,
    Vec<CoreTerm>,
);

impl CoreContract {
    fn to_signature(mut self) -> TokenStream {
        self.2.iter_mut().for_each(elim_match_form);
        self.3.iter_mut().for_each(elim_match_form);

        let mut bindings = HashMap::new();
        let has_inputs = self.0.len() > 0;
        let owns: Vec<_> = self
            .0
            .into_iter()
            .map(|arg| match arg {
                FnArg::Receiver(_) => {
                    let self_ = Ident::new("self", Span::call_site());
                    let self_repr = Ident::new("self_repr", Span::call_site());

                    bindings.insert(VarKind::Source(self_), VarKind::Source(self_repr));
                    quote!(self.own(self_repr))
                }
                FnArg::Typed(PatType { pat, .. }) => match &*pat {
                    Pat::Ident(PatIdent { ident, .. }) => {
                        let repr = Ident::new(&format!("{ident}_repr"), Span::call_site());
                        bindings.insert(
                            VarKind::Source(ident.clone()),
                            VarKind::Source(repr.clone()),
                        );
                        quote!(#ident.own(#repr))
                    }
                    _ => panic!("unsupported pattern"),
                },
            })
            .collect();

        bindings.insert(
            VarKind::Source(Ident::new("ret", Span::call_site())),
            VarKind::Source(Ident::new("ret_repr", Span::call_site())),
        );
        let mut subst = Subst { bindings };

        self.2.iter_mut().for_each(|t| {
            t.subst(&mut subst.clone());
        });

        self.3.iter_mut().for_each(|t| {
            t.subst(&mut subst.clone());
        });

        subst
            .bindings
            .remove(&VarKind::Source(Ident::new("ret", Span::call_site())));
        let requires: Vec<_> = self.2.into_iter().map(|t| core_to_sl(t)).collect();

        assert!(requires.iter().all(|a| a.clauses.len() == 1));

        let pre = requires.into_iter().reduce(|mut r1, mut r2| {
            let (mut exi1, r1) = r1.clauses.remove(0);
            let (exi2, r2) = r2.clauses.remove(0);

            exi1.extend(exi2);
            Disjuncts {
                clauses: vec![(exi1, r1.conj(r2))],
            }
        });

        let ensures: Vec<_> = self.3.into_iter().map(|t| core_to_sl(t)).collect();

        let mut pre_tokens = quote! { requires { emp } };

        if let Some((forall, req)) = pre.map(|mut p| p.clauses.remove(0)) {
            pre_tokens = quote! {
            forall #(#forall),* .
                requires { #(#owns *)* $#req$ }
            };
        } else {
            if has_inputs {
                let forall = subst.bindings.values();
                pre_tokens = quote! { forall #(#forall),* . requires {  #(#owns*)* emp }}
            }
        };

        let mut post_tokens = Vec::new();

        let post = ensures
            .into_iter()
            .reduce(|mut r1, r2| {
                r1.clauses.extend(r2.clauses);
                r1
            })
            .unwrap_or_else(|| Disjuncts { clauses: vec![] });
        for (exi, p) in post.clauses {
            let exi_toks = quote! { exists #(#exi,)* ret_repr . };

            post_tokens.push(quote! {
                #exi_toks ensures { ret.own(ret_repr) * $#p$ }
            });
        }

        quote! {
            #pre_tokens
            #(#post_tokens)*
        }
    }
}

#[proc_macro_attribute]
pub fn requires(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    match requires_inner(args, input) {
        Ok(e) => e.into(),
        Err(e) => e.into_compile_error().into(),
    }
}

fn requires_inner(args: TokenStream_, input: TokenStream_) -> syn::Result<TokenStream> {
    let term = syn::parse(args)?;
    let atrail: AttrTrail = syn::parse(input)?;

    let (mut contract, rest) = atrail.extract_contract()?;
    contract.2.push(term);
    let core = contract.elaborate()?;

    core.to_signature();

    let AttrTrail(attrs, vis, sig, rest) = rest;
    Ok(quote!(
      #(#attrs)*
      #vis #sig #rest
    ))
}

#[proc_macro_attribute]
pub fn ensures(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    match ensures_inner(args, input) {
        Ok(e) => e.into(),
        Err(e) => e.into_compile_error().into(),
    }
}

fn ensures_inner(args: TokenStream_, input: TokenStream_) -> syn::Result<TokenStream> {
    let term = syn::parse(args)?;
    let atrail: AttrTrail = syn::parse(input)?;

    let (mut contract, rest) = atrail.extract_contract()?;
    contract.3.push(term);
    let core = contract.elaborate()?;

    let spec = core.to_signature();
    let AttrTrail(attrs, vis, sig, rest) = rest;

    Ok(quote!(
      #(#attrs)*
      # [ gilogic :: macros :: specification ( #spec ) ]
      #vis #sig #rest
    ))
}
