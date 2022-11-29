#![feature(rustc_attrs)]
#![feature(register_tool)]
#![feature(extend_one)]
#![register_tool(gillian)]

extern crate proc_macro;
use proc_macro::TokenStream as TokenStream_;
use quote::ToTokens;
use syn::parse_macro_input;

mod gillian_quote;
mod gillian_syn;

use gillian_syn::*;

use assertion::Assertion;
use predicate::Predicate;

#[proc_macro_attribute]
pub fn predicate(_args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    parse_macro_input!(input as Predicate)
        .to_token_stream()
        .into()
}

#[proc_macro_attribute]
pub fn requires(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    spec::requires(args, input)
}
#[proc_macro_attribute]
pub fn ensures(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    spec::ensures(args, input)
}

#[proc_macro]
pub fn assertion(input: TokenStream_) -> TokenStream_ {
    parse_macro_input!(input as Assertion)
        .to_token_stream()
        .into()
}
