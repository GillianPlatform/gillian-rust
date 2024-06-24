extern crate proc_macro;
use anf::{term_to_core, CoreTerm};
use itertools::{Either, Itertools};
use pearlite_syn::Term;
use proc_macro::TokenStream as TokenStream_;
use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse::Parse, Attribute};

use crate::anf::{core_to_sl, elim_match_form, print_gilsonite, Disjuncts};

mod anf;

struct AttrTrail(Vec<Attribute>, TokenStream);

impl Parse for AttrTrail {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(AttrTrail(Attribute::parse_outer(input)?, input.parse()?))
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

        Ok((RawContract(pre, post), self))
    }
}

// Here we should have one term as a pre and many as a disjunction of posts but that's not what is actually being encoded here.
struct RawContract(Vec<Term>, Vec<Term>);

impl RawContract {
    fn elaborate(self) -> syn::Result<CoreContract> {
        let pres = self
            .0
            .into_iter()
            .map(term_to_core)
            .collect::<syn::Result<_>>()?;
        let posts = self
            .1
            .into_iter()
            .map(term_to_core)
            .collect::<syn::Result<_>>()?;
        Ok(CoreContract(pres, posts))
    }
}

struct CoreContract(Vec<CoreTerm>, Vec<CoreTerm>);

impl CoreContract {
    fn to_signature(mut self) -> TokenStream {
        self.0.iter_mut().for_each(elim_match_form);
        self.1.iter_mut().for_each(elim_match_form);

        let requires: Vec<_> = self.0.into_iter().map(|t| core_to_sl(t)).collect();

        assert!(requires.iter().all(|a| a.clauses.len() == 1));

        let pre = requires.into_iter().reduce(|mut r1, mut r2| {
            let (mut exi1, r1) = r1.clauses.remove(0);
            let (exi2, r2) = r2.clauses.remove(0);

            exi1.extend(exi2);
            Disjuncts {
                clauses: vec![(exi1, r1.conj(r2))],
            }
        });

        let ensures: Vec<_> = self.1.into_iter().map(|t| core_to_sl(t)).collect();

        let mut pre_tokens = quote! { requires { emp } };
        if let Some((forall, req)) = pre.map(|mut p| p.clauses.remove(0)) {
            pre_tokens = quote! {
            forall #(#forall)* .
                requires { (#req) }
            };
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
            let mut exi_toks = TokenStream::new();
            if exi.len() > 0 {
                exi_toks = quote! { exists #(#exi)* . };
            }
            post_tokens.push(quote! {
                #exi_toks ensures { (#p) }
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
    contract.0.push(term);
    let core = contract.elaborate()?;

    core.to_signature();

    let AttrTrail(sig, rest) = rest;
    Ok(quote!(
      #(#sig)*
      #rest
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
    contract.1.push(term);
    let core = contract.elaborate()?;

    let spec = core.to_signature();
    let AttrTrail(sig, rest) = rest;
    eprintln!( "{spec}");
    Ok(quote!(
      #(#sig)*
      # [ gilogic :: macros :: specification ( #spec ) ]
      #rest
    ))
}
