extern crate proc_macro;
use proc_macro::TokenStream as TokenStream_;
use proc_macro2::TokenStream;
use quote::quote;

#[proc_macro_attribute]
pub fn requires(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    let args: TokenStream = args.into();
    let input: TokenStream = input.into();
    quote!(
      #[cfg(creusot)]
      #[::creusot_contracts::requires(#args)]
      #input

      #[cfg(gillian)]
      #[::gilogic::macros::requires(#args)]
      #input

      #[cfg(not(any(gillian, creusot)))]
      #input
    )
    .into()
}

#[proc_macro_attribute]
pub fn ensures(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    let args: TokenStream = args.into();
    let input: TokenStream = input.into();
    quote!(
      #[cfg(creusot)]
      #[::creusot_contracts::ensures(#args)]
      #input

      #[cfg(gillian)]
      #[::gilogic::macros::ensures(#args)]
      #input

      #[cfg(not(any(gillian, creusot)))]
      #input
    )
    .into()
}
