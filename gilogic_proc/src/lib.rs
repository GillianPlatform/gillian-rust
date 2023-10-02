#![feature(rustc_attrs)]
#![feature(register_tool)]
#![register_tool(gillian)]
#![feature(box_patterns)]

extern crate proc_macro;
use ::quote::ToTokens;
use proc_macro::TokenStream as TokenStream_;
use syn::parse_macro_input;

pub(crate) mod visitors;

mod borrows;
mod folding;
mod gilogic_syn;
mod lifetime_hack;
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
pub fn with_freeze_lemma_for_mutref(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    match FreezeMutRefOwn::parse(args, input) {
        Ok(freeze_mut_own_ref) => freeze_mut_own_ref.to_token_stream().into(),
        Err(err) => err.to_compile_error().into(),
    }
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
pub fn open_borrow(input: TokenStream_) -> TokenStream_ {
    folding::add_to_call_name(input, "_____unfold")
}

#[proc_macro]
pub fn close_borrow(input: TokenStream_) -> TokenStream_ {
    folding::add_to_call_name(input, "_____fold")
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
