use std::fmt::Debug;

use proc_macro2::Span;
use quote::ToTokens;
use syn::{
    buffer::Cursor,
    parenthesized,
    parse::{discouraged::Speculative, Parse, ParseStream},
    token,
    token::Token,
    Error, Expr, Ident, Token,
};

use crate::formula::Formula;

pub enum SimpleAssertion {
    Emp(Span),
    Pure(Box<Formula>),
    PointsTo(Ident, Token![-], Token![>], Box<Expr>),
}

impl Debug for SimpleAssertion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SimpleAssertion::Emp(..) => write!(f, "emp"),
            SimpleAssertion::Pure(form) => form.fmt(f),
            SimpleAssertion::PointsTo(id, _, _, exp) => {
                write!(f, "({} -> {})", id, exp.to_token_stream())
            }
        }
    }
}

impl SimpleAssertion {
    fn parse_points_to_inner(input: ParseStream) -> syn::Result<Self> {
        let left: Ident = input.parse()?;
        let arrow_dash: Token![-] = input.parse()?;
        let arrow_point: Token![>] = input.parse()?;
        let rvalue: Expr = input.parse()?;
        Ok(SimpleAssertion::PointsTo(
            left,
            arrow_dash,
            arrow_point,
            Box::new(rvalue),
        ))
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
            let ident: Ident = input.parse().unwrap();
            return Ok(Self::Emp(ident.span()));
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

pub struct Assertion {
    pub(crate) lvars: Vec<Ident>,
    pub(crate) inner: AssertionInner,
}

/// An assertion is the "star" of a bunch of simple assertions.
/// That's probably how we should formalize it too.
pub enum AssertionInner {
    Leaf(SimpleAssertion),
    Star {
        left: Box<AssertionInner>,
        right: Box<AssertionInner>,
        star_token: Token![*],
    },
}

struct Accumulator {
    current: Option<AssertionInner>,
    trailing_token: Option<Token![*]>,
}

impl Accumulator {
    fn new() -> Self {
        Self {
            current: None,
            trailing_token: None,
        }
    }

    fn push_star(&mut self, token: Token![*]) {
        match self.trailing_token {
            None => self.trailing_token = Some(token),
            Some(..) => panic!("Pushed two tokens in a row"),
        }
    }

    fn push_simple_assertion(&mut self, sasrt: SimpleAssertion) {
        let token = self.trailing_token.take();
        let new_assertion = AssertionInner::Leaf(sasrt);
        let current = self.current.take();
        match current {
            None => {
                assert!(
                    token.is_none(),
                    "Pushed a token without a current assertion"
                );
                self.current = Some(new_assertion)
            }
            Some(asrt) => {
                let token = token.expect("Pushed two assertions in a row");
                self.current = Some(AssertionInner::Star {
                    left: Box::new(asrt),
                    right: Box::new(new_assertion),
                    star_token: token,
                });
            }
        }
    }

    fn into_assert(self) -> AssertionInner {
        match self.current {
            None => panic!("No assertion"),
            Some(asrt) => {
                assert!(self.trailing_token.is_none(), "Trailing token");
                asrt
            }
        }
    }
}

impl Parse for AssertionInner {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut acc = Accumulator::new();

        loop {
            let sasrt = SimpleAssertion::parse(input)?;
            acc.push_simple_assertion(sasrt);
            if !<Token![*]>::peek(input.cursor()) {
                break;
            }
            let star = input.parse()?;
            acc.push_star(star);
        }

        Ok(acc.into_assert())
    }
}

impl Parse for Assertion {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lvars = if input.peek(Token![|]) {
            let _: Token![|] = input.parse()?;
            let mut lvars = Vec::with_capacity(2);
            loop {
                let lvar: Ident = input.parse()?;
                lvars.push(lvar);
                if !input.peek(Token![,]) {
                    break;
                }
                let _: Token![,] = input.parse()?;
            }
            let _: Token![|] = input.parse()?;
            lvars
        } else {
            Vec::new()
        };
        let inner = input.parse()?;
        Ok(Self { lvars, inner })
    }
}
