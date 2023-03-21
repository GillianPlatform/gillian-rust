#![feature(rustc_attrs)]
#![feature(register_tool)]
#![register_tool(gillian)]

extern crate proc_macro;
use ::quote::ToTokens;
use proc_macro::TokenStream as TokenStream_;
use syn::parse_macro_input;

mod borrows;
mod gilogic_syn;
mod quote;
mod spec;

use gilogic_syn::*;

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

#[proc_macro_attribute]
pub fn lemma(_args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    parse_macro_input!(input as Lemma).to_token_stream().into()
}

#[proc_macro_attribute]
pub fn show_safety(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    spec::show_safety(args, input)
}

#[proc_macro_attribute]
pub fn borrow(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    borrows::borrow(args, input)
}

#[proc_macro]
pub fn assertion(input: TokenStream_) -> TokenStream_ {
    match parse_macro_input!(input as Assertion).encode() {
        Ok(stream) => stream.into(),
        Err(error) => error.to_compile_error().into(),
    }
}

#[proc_macro]
pub fn assertion_test(input: TokenStream_) -> TokenStream_ {
    dbg!(parse_macro_input!(input as Assertion));
    panic!("stop");
}
