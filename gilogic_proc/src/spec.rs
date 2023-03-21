use proc_macro::TokenStream as TokenStream_;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{
    parse_macro_input, punctuated::Punctuated, FnArg, ImplItemMethod, PatType, ReturnType, Token,
};
use uuid::Uuid;

use super::gilogic_syn::Assertion;

pub(crate) fn requires(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    // I'm using `ImplItemMethod` here, but it could be an `FnItem`.
    // However, an `FnItem` is just `ImplItemMethod` that cannot have the `default` keyword,
    // so I'm expecting this to work in any context.
    let item = parse_macro_input!(input as ImplItemMethod);
    let assertion: TokenStream = match parse_macro_input!(args as Assertion).encode() {
        Ok(stream) => stream.into(),
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
    let result = quote! {
        #[cfg(gillian)]
        #[rustc_diagnostic_item=#name_string]
        #[gillian::decl::precondition]
        #[gillian::decl::pred_ins=""]
        fn #name #generics (#inputs) -> ::gilogic::RustAssertion {
           ::gilogic::__stubs::defs([#assertion])
        }

        #[gillian::spec::precondition=#name_string]
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
        Ok(stream) => stream.into(),
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
    let result = quote! {
        #[cfg(gillian)]
        #[rustc_diagnostic_item=#name_string]
        #[gillian::decl::postcondition]
        #[gillian::decl::pred_ins=#ins]
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
