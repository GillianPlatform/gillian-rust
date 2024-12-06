use proc_macro::TokenStream as TokenStream_;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse::Parse, parse_macro_input, parse_quote, punctuated::Punctuated, Attribute, ExprClosure,
    FnArg, ImplItemFn, Pat, PatIdent, PatType, ReturnType, Signature, Token,
};
use uuid::Uuid;

mod aux {
    use syn::{parse::Parse, punctuated::Punctuated, LitStr, Token};

    use crate::gilogic_syn::LvarDecl;

    pub(crate) struct CommaSepLvarDecl(#[allow(dead_code)] pub Punctuated<LvarDecl, Token![,]>);

    impl Parse for CommaSepLvarDecl {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            Punctuated::parse_terminated(input).map(CommaSepLvarDecl)
        }
    }

    pub(crate) struct LvarsAttr(#[allow(dead_code)] pub CommaSepLvarDecl);
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
        attr.path().leading_colon.is_none()
            && attr.path().segments.len() == looked_for.len()
            && attr
                .path()
                .segments
                .iter()
                .zip(looked_for)
                .all(|(seg, name)| seg.ident == name && seg.arguments.is_empty())
    })
}

enum Specifiable {
    Fn(ImplItemFn),
    Closure(ExprClosure),
}

impl Parse for Specifiable {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        todo!()
    }
}

impl Specifiable {
    fn attrs(&self) -> &[Attribute] {
        match self {
            Specifiable::Fn(f) => &f.attrs,
            Specifiable::Closure(c) => &c.attrs,
        }
    }
}

impl ToTokens for Specifiable {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        todo!()
    }
}

use crate::Specification;

pub(crate) fn specification(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    // I'm using `ImplItemMethod` here, but it could be an `FnItem`.
    // However, an `FnItem` is just `ImplItemMethod` that cannot have the `default` keyword,
    // so I'm expecting this to work in any context.
    let item = parse_macro_input!(input as ImplItemFn);
    let parsed_spec = parse_macro_input!(args as Specification);

    let (toks, name_string) = match compile_spec(&parsed_spec, &item.attrs, &item.sig) {
        Ok(s) => s,
        Err(error) => return error.to_compile_error().into(),
    };

    let result = quote! {
        #toks

        #[gillian::spec=#name_string]
        #item
    };

    result.into()
}

pub(crate) fn compile_spec(
    spec: &Specification,
    attrs: &[Attribute],
    sig: &Signature,
) -> syn::Result<(TokenStream, String)> {
    // let attrs = subject.attrs();

    let id = Uuid::new_v4().to_string();
    let name = {
        let ident = sig.ident.to_string();
        let name_with_uuid = format!("{}_spec_{}", ident, id).replace('-', "_");
        format_ident!("{}", name_with_uuid, span = Span::call_site())
    };
    let name_string = name.to_string();

    let mut inputs = sig.inputs.clone();
    let ins = format!("{}", inputs.len());
    let generics = &sig.generics;

    let ret_ty = match &sig.output {
        ReturnType::Default => quote! { () },
        ReturnType::Type(_token, ty) => quote! { #ty },
    };

    inputs.push(parse_quote! { ret : #ret_ty});

    let spec: TokenStream = spec.encode()?;

    let for_lemma = if get_attr(&attrs, &["gillian", "decl", "lemma"]).is_some() {
        Some(quote!(#[gillian::for_lemma]))
    } else {
        None
    };

    let trusted = if get_attr(&attrs, &["gillian", "trusted"]).is_some() {
        Some(quote!(#[gillian::trusted]))
    } else {
        None
    };

    let timeless = if get_attr(&attrs, &["gillian", "timeless"]).is_some() {
        Some(quote!(#[gillian::timeless]))
    } else {
        None
    };

    let result = quote! {
        #[cfg(gillian)]
        #[rustc_diagnostic_item=#name_string]
        #for_lemma #trusted #timeless
        #[gillian::decl::specification]
        #[gillian::decl::pred_ins=#ins]
        fn #name #generics (#inputs) -> gilogic::RustAssertion {
           #spec
        }
    };
    Ok((result, name_string))
}

pub(crate) fn show_safety(_args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    let item = parse_macro_input!(input as ImplItemFn);
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
        quote! { gilogic::__stubs::emp() }
    } else {
        args_own.to_token_stream()
    };
    let result = quote! {
        #[gilogic::macros::specification(
            requires { #req }
            ensures { ret.own() }
        )]
        #item
    };
    result.into()
}
