#![feature(rustc_attrs)]
#![feature(register_tool)]
#![register_tool(gillian)]

extern crate proc_macro;
use proc_macro::TokenStream as TokenStream_;
use quote::quote;
use syn::parse_macro_input;

mod gillian_quote;
mod gillian_syn;

use gillian_syn::*;

use predicate::Predicate;

#[proc_macro_attribute]
pub fn predicate(_args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    let x = parse_macro_input!(input as Predicate);
    quote!(
        #x
    )
    .into()
}
