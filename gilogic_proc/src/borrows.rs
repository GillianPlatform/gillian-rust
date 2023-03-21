use proc_macro::TokenStream as TokenStream_;
use quote::{format_ident, quote};
use syn::{parse_macro_input, ImplItemMethod};
use uuid::Uuid;

pub fn borrow(_args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    let item = parse_macro_input!(input as ImplItemMethod);

    let borrow_id = Uuid::new_v4().to_string();
    let close_token_diag = format!("close_token_{borrow_id}");
    let borrow_token = item.sig.clone();

    let mut close_token = item.sig;
    let close_token_ident = format_ident!("___{}__close_token", close_token.ident);
    close_token.ident = close_token_ident;

    quote! {
      #[gillian::close_token = #close_token_diag]
      #[::gilogic::macros::predicate]
      #borrow_token;

      #[rustc_diagnostic_item = #close_token_diag]
      #[::gilogic::macros::predicate]
      #close_token;
    }
    .into()
}
