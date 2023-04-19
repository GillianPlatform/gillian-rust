use proc_macro2::TokenStream;
use quote::quote;
use syn::{FnArg, GenericParam, LifetimeDef, PatType, Receiver, Signature, Type};
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

pub(crate) fn generic_lifetimes_attr(sig: &Signature) -> TokenStream {
    let str = generic_lifetimes(sig).join(",");
    quote!(#[gillian::parameters::lifetimes=#str])
}
