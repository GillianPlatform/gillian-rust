use syn::{
    parenthesized,
    parse::{Parse, ParseStream},
    spanned::Spanned,
    Attribute,
};

use crate::gilogic_syn::{AsrtFragment, Assertion, Lemma};

pub struct ExtractLemma(pub Lemma);

fn get_attribute(attrs: &[Attribute], name: &str) -> Option<Attribute> {
    attrs
        .iter()
        .find(|attr| attr.path.segments.last().map_or(false, |x| x.ident == name))
        .cloned()
}

fn check_just_call(asrt: &Assertion) -> bool {
    asrt.def.len() == 1 && matches!(asrt.def[0], AsrtFragment::PredCall(..))
}

fn parse_asrt_in_parens(input: ParseStream) -> syn::Result<Assertion> {
    let content;
    parenthesized!(content in input);
    content.parse()
}

impl Parse for ExtractLemma {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let lemma = input.parse::<Lemma>()?;
        let requires_attr = get_attribute(&lemma.attributes, "requires")
            .ok_or_else(|| syn::Error::new(lemma.sig.span(), "Lemma doesn't have a `requires`"))?;
        let span = requires_attr.span();
        let require_asrt = syn::parse::Parser::parse2(parse_asrt_in_parens, requires_attr.tokens)?;
        if !check_just_call(&require_asrt) {
            return Err(syn::Error::new(
                span,
                "extract_lemma's `requires` must be a single predicate call",
            ));
        }

        let ensures_attr = get_attribute(&lemma.attributes, "ensures")
            .ok_or_else(|| syn::Error::new(lemma.sig.span(), "Lemma doesn't have a `ensures`"))?;
        let span = ensures_attr.span();
        let ensure_asrt = syn::parse::Parser::parse2(parse_asrt_in_parens, ensures_attr.tokens)?;
        if !check_just_call(&ensure_asrt) {
            return Err(syn::Error::new(
                span,
                "extract_lemma's `ensures` must be a single predicate call",
            ));
        }

        Ok(Self(lemma))
    }
}
