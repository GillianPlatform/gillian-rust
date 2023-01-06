use proc_macro::TokenStream as TokenStream_;
use proc_macro2::Span;
use quote::{format_ident, quote};
use syn::{parse_macro_input, ImplItemMethod, ReturnType};
use uuid::Uuid;

use super::assertion::Assertion;

// fn retrieve_name_in_pat(pat: &Pat) -> String {
//     match pat {
//         Pat::Box(pbox) => retrieve_name_in_pat(&pbox.pat),
//         Pat::Ident(pid) => pid.ident.to_string(),
//         Pat::Reference(pref) => retrieve_name_in_pat(&pref.pat),
//         Pat::Type(tpat) => retrieve_name_in_pat(&tpat.pat),
//         Pat::Path(_) => panic!("Cannot retrieve name in path pattern for specification"),
//         Pat::Lit(_) => panic!("Cannot retrieve name in literal pattern for specification"),
//         Pat::Macro(_) => panic!("Cannot retrieve name in macro pattern for specification"),
//         Pat::Or(_) => panic!("Cannot retrieve name in or pattern for specification"),
//         Pat::Range(_) => panic!("Cannot retrieve name in range pattern for specification"),
//         Pat::Rest(_) => panic!("Cannot retrieve name in rest pattern for specification"),
//         Pat::Slice(_) => panic!("Cannot retrieve name in slice pattern for specification"),
//         Pat::Struct(_) => panic!("Cannot retrieve name in struct pattern for specification"),
//         Pat::Tuple(_) => panic!("Cannot retrieve name in tuple pattern for specification"),
//         Pat::TupleStruct(_) => {
//             panic!("Cannot retrieve name in tuple struct pattern for specification")
//         }
//         Pat::Verbatim(_) => panic!("Cannot retrieve name in verbatim pattern for specification"),
//         Pat::Wild(_) => panic!("Cannot retrieve name in wildcard pattern for specification"),
//         &_ => panic!("Cannot retrieve name in unknown pattern for specification"),
//     }
// }

// fn retrieve_name_in_arg(arg: &FnArg) -> String {
//     match arg {
//         FnArg::Receiver(_) => "self".to_string(),
//         FnArg::Typed(typed) => retrieve_name_in_pat(&typed.pat),
//     }
// }

pub(crate) fn requires(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    // I'm using `ImplItemMethod` here, but it could be an `FnItem`.
    // However, an `FnItem` is just `ImplItemMethod` that cannot have the `default` keyword,
    // so I'm expecting this to work in any context.
    let item = parse_macro_input!(input as ImplItemMethod);
    let assertion = parse_macro_input!(args as Assertion);
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
    let assertion = parse_macro_input!(args as Assertion);
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
