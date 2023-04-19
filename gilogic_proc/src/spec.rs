use proc_macro::TokenStream as TokenStream_;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse_macro_input, punctuated::Punctuated, token::Colon, Attribute, FnArg, ImplItemMethod, Pat,
    PatIdent, PatType, ReturnType, Token,
};
use uuid::Uuid;

mod aux {
    use syn::{parse::Parse, punctuated::Punctuated, LitStr, Token};

    use crate::gilogic_syn::LvarDecl;

    pub(crate) struct CommaSepLvarDecl(pub Punctuated<LvarDecl, Token![,]>);

    impl Parse for CommaSepLvarDecl {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            Punctuated::parse_terminated(input).map(CommaSepLvarDecl)
        }
    }

    pub(crate) struct LvarsAttr(pub CommaSepLvarDecl);
    impl Parse for LvarsAttr {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            input.parse::<Token![=]>()?;
            let str: LitStr = input.parse()?;
            let ret = syn::parse_str(&str.value())?;
            Ok(LvarsAttr(ret))
        }
    }
}

fn get_attr<'a>(
    attrs: &'a [Attribute],
    looked_for: &'static [&'static str],
) -> Option<&'a Attribute> {
    attrs.iter().find(|attr| {
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

use crate::gilogic_syn::LvarDecl;

use super::gilogic_syn::Assertion;

pub(crate) fn requires(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    // I'm using `ImplItemMethod` here, but it could be an `FnItem`.
    // However, an `FnItem` is just `ImplItemMethod` that cannot have the `default` keyword,
    // so I'm expecting this to work in any context.
    let item = parse_macro_input!(input as ImplItemMethod);
    let parsed_assertion = parse_macro_input!(args as Assertion);
    let assertion: TokenStream = match parsed_assertion.encode() {
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

    let lifetimes = super::lifetime_hack::generic_lifetimes_attr(&item.sig);

    let lvar_list = parsed_assertion.lvars.to_token_stream().to_string();

    let for_lemma = if get_attr(&item.attrs, &["gillian", "decl", "lemma"]).is_some() {
        Some(quote!(#[gillian::for_lemma]))
    } else {
        None
    };

    let result = quote! {
        #[cfg(gillian)]
        #[rustc_diagnostic_item=#name_string]
        #for_lemma
        #[gillian::decl::precondition]
        #[gillian::decl::pred_ins=""]
        #lifetimes
        fn #name #generics (#inputs) -> ::gilogic::RustAssertion {
           ::gilogic::__stubs::defs([#assertion])
        }

        #[gillian::spec::precondition=#name_string]
        #[gillian::spec::precondition::lvars=#lvar_list]
        #lifetimes
        #item
    };
    result.into()
}

pub(crate) fn ensures(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    // I'm using `ImplItemMethod` here, but it could be an `FnItem`.
    // However, an `FnItem` is just `ImplItemMethod` that cannot have the `default` keyword,
    // so I'm expecting this to work in any context.
    let item = parse_macro_input!(input as ImplItemMethod);
    let mut parsed_assertion = parse_macro_input!(args as Assertion);

    // We create an lvar for each lvar already declared in the pre
    if let Some(lvars_attr) = get_attr(&item.attrs, &["gillian", "spec", "precondition", "lvars"]) {
        let pre_lvars: syn::Result<aux::LvarsAttr> = syn::parse2(lvars_attr.tokens.clone());
        match pre_lvars {
            Ok(lvars) => parsed_assertion.lvars.extend(lvars.0 .0),
            Err(error) => return error.to_compile_error().into(),
        }
    }

    // We create an lvar for each argument
    let f_args_lvars: Punctuated<LvarDecl, Token![,]> = item
        .sig
        .inputs
        .iter()
        .filter_map(|arg| match arg {
            FnArg::Typed(PatType {
                pat: box Pat::Ident(id),
                ty,
                ..
            }) => Some(LvarDecl {
                ident: id.ident.clone(),
                ty_opt: Some((Colon::default(), *ty.clone())),
            }),
            _ => None,
        })
        .collect();
    parsed_assertion.lvars.extend(f_args_lvars);

    let assertion: TokenStream = match parsed_assertion.encode() {
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
    let lifetimes = super::lifetime_hack::generic_lifetimes_attr(&item.sig);

    let for_lemma = if get_attr(&item.attrs, &["gillian", "decl", "lemma"]).is_some() {
        Some(quote!(#[gillian::for_lemma]))
    } else {
        None
    };

    let result = quote! {
        #[cfg(gillian)]
        #[rustc_diagnostic_item=#name_string]
        #for_lemma
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
            FnArg::Typed(PatType {
                pat: box Pat::Ident(PatIdent { ident, .. }),
                ..
            }) => quote!(#ident.own()),
            _ => panic!("Invalid argument pattern for show_safety: {:?}", arg),
        })
        .collect();
    let req = if args_own.is_empty() {
        quote! { ::gilogic::__stubs::emp() }
    } else {
        args_own.to_token_stream()
    };
    let result = quote! {
        #[::gilogic::macros::requires(#req)]
        #[::gilogic::macros::ensures(ret.own())]
        #item
    };
    result.into()
}
