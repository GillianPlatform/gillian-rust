use proc_macro2::Span;
use syn::{parse::Parse, Attribute, Block, Error, Signature, Token};

use crate::Specification;

pub struct Lemma {
    pub(crate) attributes: Vec<Attribute>,
    pub(crate) pub_token: Option<Token![pub]>,
    pub(crate) specification: Specification,
    pub(crate) sig: Signature,
    pub(crate) body: Option<Block>,
}

impl Parse for Lemma {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let attributes = input.call(Attribute::parse_outer)?;

        let (specification_attr, attributes) : (Vec<_>, _) = attributes
            .into_iter()
            .partition(|attr| attr.path().segments.last().unwrap().ident == "specification");

        let specification = match specification_attr.get(0) {
            Some(e) =>{ e.parse_args::<Specification>()? },
            None => return Err(Error::new(Span::call_site(), "need specification below lemma"))
        };

        let pub_token = if input.lookahead1().peek(Token![pub]) {
            Some(input.parse()?)
        } else {
            None
        };
        let sig: Signature = input.parse()?;
        let body = if input.lookahead1().peek(Token![;]) {
            let _: Token![;] = input.parse().unwrap();
            None
        } else {
            Some(input.parse()?)
        };
        Ok(Lemma {
            attributes,
            specification,
            pub_token,
            sig,
            body,
        })
    }
}
