use proc_macro::TokenStream as TokenStream_;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{
    parse_macro_input, punctuated::Punctuated, Attribute, FnArg, GenericParam, ImplItemMethod,
    LifetimeDef, PatType, Receiver, ReturnType, Signature, Token, Type,
};
use uuid::Uuid;

fn generic_lifetimes(sig: &Signature) -> Vec<String> {
    let explicit_lfts: Vec<_> = sig
        .generics
        .params
        .iter()
        .filter_map(|x| {
            if let GenericParam::Lifetime(LifetimeDef { lifetime, .. }) = x {
                Some(lifetime.ident.to_string())
            } else {
                None
            }
        })
        .collect();

    if !explicit_lfts.is_empty() {
        return explicit_lfts;
    }

    for arg in &sig.inputs {
        match arg {
            FnArg::Receiver(Receiver {
                reference: Some(..),
                ..
            })
            | FnArg::Typed(PatType {
                ty: box Type::Reference(..),
                ..
            }) => return vec!["a".to_string()],
            _ => continue,
        }
    }
    vec![]
}

fn generic_lifetimes_string(sig: &Signature) -> String {
    generic_lifetimes(sig).join(",")
}

fn has_attr(attrs: &[Attribute], looked_for: &[&str]) -> bool {
    attrs.iter().any(|attr| {
        attr.path.leading_colon.is_none()
            && attr.path.segments.len() == looked_for.len()
            && attr
                .path
                .segments
                .iter()
                .zip(looked_for)
                .all(|(seg, name)| seg.ident == name && seg.arguments.is_empty())
    })
}

use super::gilogic_syn::Assertion;

pub(crate) fn requires(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    // I'm using `ImplItemMethod` here, but it could be an `FnItem`.
    // However, an `FnItem` is just `ImplItemMethod` that cannot have the `default` keyword,
    // so I'm expecting this to work in any context.
    let item = parse_macro_input!(input as ImplItemMethod);
    let assertion: TokenStream = match parse_macro_input!(args as Assertion).encode() {
        Ok(stream) => stream,
        Err(error) => return error.to_compile_error().into(),
    };
    let id = Uuid::new_v4().to_string();
    let name = {
        let ident = item.sig.ident.to_string();
        let name_with_uuid = format!("{}_pre_{}", ident, id).replace('-', "_");
        format_ident!("{}", name_with_uuid, span = Span::call_site())
    };
    let name_string = name.to_string();
    let inputs = &item.sig.inputs;
    let generics = &item.sig.generics;

    let gen_lft_str = generic_lifetimes_string(&item.sig);
    let lft_params = quote!(#[gillian::parameters::lifetimes=#gen_lft_str]);
    let lifetimes = if has_attr(
        &item.attrs,
        &["gillian", "lemma", "produces_lifetime_token"],
    ) {
        None
    } else {
        Some(quote!(#lft_params))
    };

    let result = quote! {
        #[cfg(gillian)]
        #[rustc_diagnostic_item=#name_string]
        #[gillian::decl::precondition]
        #[gillian::decl::pred_ins=""]
        #lifetimes
        fn #name #generics (#inputs) -> ::gilogic::RustAssertion {
           ::gilogic::__stubs::defs([#assertion])
        }

        #[gillian::spec::precondition=#name_string]
        #lft_params
        #item
    };
    result.into()
}

pub(crate) fn ensures(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    // I'm using `ImplItemMethod` here, but it could be an `FnItem`.
    // However, an `FnItem` is just `ImplItemMethod` that cannot have the `default` keyword,
    // so I'm expecting this to work in any context.
    let item = parse_macro_input!(input as ImplItemMethod);
    let assertion: TokenStream = match parse_macro_input!(args as Assertion).encode() {
        Ok(stream) => stream,
        Err(error) => return error.to_compile_error().into(),
    };
    let id = Uuid::new_v4().to_string();
    let name = {
        let ident = item.sig.ident.to_string();
        let name_with_uuid = format!("{}_post_{}", ident, id).replace('-', "_");
        format_ident!("{}", name_with_uuid, span = Span::call_site())
    };
    let name_string = name.to_string();
    let ins = "0";
    let ret_ty = match &item.sig.output {
        ReturnType::Default => quote! { () },
        ReturnType::Type(_token, ty) => quote! { #ty },
    };
    let generics = &item.sig.generics;
    let gen_lft_str = generic_lifetimes_string(&item.sig);
    let lifetimes = if has_attr(
        &item.attrs,
        &["gillian", "lemma", "consumes_lifetime_token"],
    ) {
        None
    } else {
        Some(quote!(#[gillian::parameters::lifetime_params=#gen_lft_str]))
    };
    let result = quote! {
        #[cfg(gillian)]
        #[rustc_diagnostic_item=#name_string]
        #[gillian::decl::postcondition]
        #[gillian::decl::pred_ins=#ins]
        #lifetimes
        fn #name #generics (ret: #ret_ty) -> ::gilogic::RustAssertion {
           ::gilogic::__stubs::defs([#assertion])
        }

        #[gillian::spec::postcondition=#name_string]
        #item
    };
    result.into()
}

pub(crate) fn show_safety(_args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    let item = parse_macro_input!(input as ImplItemMethod);
    let args_own: Punctuated<TokenStream, Token![*]> = item
        .sig
        .inputs
        .iter()
        .map(|arg| match arg {
            FnArg::Receiver(_receiver) => quote!(self.own()),
            FnArg::Typed(PatType { pat, .. }) => quote!(#pat.own()),
        })
        .collect();
    let result = quote! {
        #[::gilogic::macros::requires(#args_own)]
        #[::gilogic::macros::ensures(ret.own())]
        #item
    };
    result.into()
}
