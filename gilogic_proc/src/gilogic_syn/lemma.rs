use syn::{parse::Parse, Attribute, Block, Signature, Token};

pub struct Lemma {
    pub(crate) attributes: Vec<Attribute>,
    pub(crate) sig: Signature,
    pub(crate) body: Option<Block>,
}

impl Parse for Lemma {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let attributes = input.call(Attribute::parse_outer)?;
        let sig: Signature = input.parse()?;
        let body = if input.lookahead1().peek(Token![;]) {
            let _: Token![;] = input.parse().unwrap();
            None
        } else {
            Some(input.parse()?)
        };
        Ok(Lemma {
            attributes,
            sig,
            body,
        })
    }
}
