use crate::gilogic_syn::*;
use proc_macro2::TokenStream;
use syn::{
    parse::{Parse, ParseStream},
    parse_quote,
    punctuated::Punctuated,
    Token,
};

pub struct AssertBind {
    lvars: Punctuated<LvarDecl, Token![,]>,
    assertion: Assertion,
}

impl Parse for AssertBind {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let fork = input.fork();
        let res: syn::Result<Punctuated<LvarDecl, Token![,]>> =
            Punctuated::parse_separated_nonempty(&fork);
        let lvars = if res.is_ok() && fork.peek(Token![|]) {
            let lvars = Punctuated::parse_separated_nonempty(input)?;
            let _: Token![|] = input.parse()?;
            lvars
        } else {
            Punctuated::new()
        };
        let assertion = input.parse()?;
        Ok(AssertBind { lvars, assertion })
    }
}

impl AssertBind {
    pub fn encode(&self) -> syn::Result<TokenStream> {
        let AssertBind { lvars, assertion } = self;
        let assertion = assertion.encode()?;
        let let_bind = if lvars.is_empty() {
            TokenStream::new()
        } else {
            let lvar_names = lvars.iter().map(|ld| ld.ident.clone());
            parse_quote!(
                let (#(#lvar_names,)*) =
            )
        };
        let result: TokenStream = parse_quote! {
          #let_bind gilogic::__stubs::assert_bind(
            #[gillian::no_translate] |#lvars| #assertion
          );
        };
        Ok(result)
    }
}
