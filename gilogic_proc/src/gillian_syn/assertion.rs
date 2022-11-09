use std::fmt::Debug;

use quote::ToTokens;
use syn::{
    buffer::Cursor,
    parenthesized,
    parse::{discouraged::Speculative, Parse, ParseStream},
    punctuated::Punctuated,
    token, Error, Expr, Ident, Token,
};

use crate::formula::Formula;

pub enum SimpleAssertion {
    Emp,
    Pure(Box<Formula>),
    PointsTo(Ident, Box<Expr>),
}

impl Debug for SimpleAssertion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SimpleAssertion::Emp => write!(f, "emp"),
            SimpleAssertion::Pure(form) => form.fmt(f),
            SimpleAssertion::PointsTo(id, exp) => {
                write!(f, "({} -> {})", id, exp.to_token_stream())
            }
        }
    }
}

impl SimpleAssertion {
    fn parse_points_to_inner(input: ParseStream) -> syn::Result<Self> {
        let left: Ident = input.parse()?;
        let _arrow_dash: Token![-] = input.parse()?;
        let _arrow_point: Token![>] = input.parse()?;
        let rvalue: Expr = input.parse()?;
        Ok(SimpleAssertion::PointsTo(left, Box::new(rvalue)))
    }

    fn peek_emp(cursor: Cursor) -> bool {
        if let Some((ident, _rest)) = cursor.ident() {
            ident == "emp"
        } else {
            false
        }
    }
}

impl Parse for SimpleAssertion {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let fork = input.fork();
        if let Ok(formula) = fork.parse() {
            input.advance_to(&fork);
            return Ok(Self::Pure(Box::new(formula)));
        }
        if input.peek(token::Paren) {
            let inner;
            let _ = parenthesized!(inner in input);
            return inner.parse();
        }
        if Self::peek_emp(input.cursor()) {
            let _: Ident = input.parse().unwrap();
            return Ok(Self::Emp);
        }
        if input.peek(Token![#]) && input.peek2(token::Paren) {
            let _: Token![#] = input.parse().unwrap();
            let points_to_buffer;
            let _ = parenthesized!(points_to_buffer in input);
            return Self::parse_points_to_inner(&points_to_buffer);
        }
        Err(Error::new(
            input.cursor().span(),
            "Unexpected token in assertion",
        ))
    }
}

/// An assertion is the "star" of a bunch of simple assertions.
/// That's probably how we should formalize it too.
#[derive(Debug)]
pub struct Assertion(Vec<SimpleAssertion>);

impl Parse for Assertion {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let simples: Punctuated<SimpleAssertion, Token![*]> =
            Punctuated::parse_separated_nonempty(input)?;
        Ok(Assertion(simples.into_iter().collect()))
    }
}
