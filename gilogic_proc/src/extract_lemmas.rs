use syn::{
    parenthesized,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
    spanned::Spanned,
    Attribute, Token,
};

use crate::{
    gilogic_syn::{AsrtFragment, Lemma},
    Specification,
};

pub struct ExtractLemma(pub Lemma);

fn get_attribute(attrs: &[Attribute], name: &str) -> Option<Attribute> {
    attrs
        .iter()
        .find(|attr| attr.path.segments.last().map_or(false, |x| x.ident == name))
        .cloned()
}

fn check_just_call(asrt: &Punctuated<AsrtFragment, Token![*]>) -> bool {
    asrt.len() == 1 && matches!(asrt[0], AsrtFragment::PredCall(..))
}

fn check_just_call_and_pure(asrt: &Punctuated<AsrtFragment, Token![*]>) -> bool {
    let (call_seen, valid) = asrt.iter().fold((false, true), |(call_seen, valid), frag| {
        match (valid, call_seen, frag) {
            (false, _, _) | (_, _, AsrtFragment::PointsTo(..) | AsrtFragment::Observation(..)) => {
                (false, false)
            }
            (true, false, AsrtFragment::PredCall(..)) => (true, true),
            (true, true, AsrtFragment::PredCall(..)) => (false, false),
            (true, b, AsrtFragment::Pure(..) | AsrtFragment::Emp(..)) => (b, true),
        }
    });
    valid && call_seen
}

fn parse_spec_in_parens(input: ParseStream) -> syn::Result<Specification> {
    let content;
    parenthesized!(content in input);
    content.parse()
}

impl Parse for ExtractLemma {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let lemma = input.parse::<Lemma>()?;
        let spec_attr = get_attribute(&lemma.attributes, "specification").ok_or_else(|| {
            syn::Error::new(lemma.sig.span(), "Lemma doesn't have a `specification`")
        })?;
        let span = spec_attr.span();
        let spec: Specification =
            syn::parse::Parser::parse2(parse_spec_in_parens, spec_attr.tokens)?;
        let require_asrt = spec.precond;
        if !check_just_call_and_pure(&require_asrt) {
            return Err(syn::Error::new(
                span,
                "extract_lemma's `requires` must be a single predicate call",
            ));
        }

        let ensures_asrt = &spec.postconds[0].postcond;
        if !check_just_call(&ensures_asrt) {
            return Err(syn::Error::new(
                span,
                "extract_lemma's `ensures` must be a single predicate call",
            ));
        }

        Ok(Self(lemma))
    }
}
