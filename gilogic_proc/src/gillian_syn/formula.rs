use std::fmt::Debug;

use quote::ToTokens;
use syn::{
    parse::{Parse, ParseStream},
    spanned::Spanned,
    BinOp, Error, Expr,
};

pub enum Formula {
    Eq(Box<Expr>, Box<Expr>),
}

impl TryFrom<Expr> for Formula {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self, Self::Error> {
        let err = Err(Error::new(value.span(), "Expr is not a formula"));
        let binary = match value {
            Expr::Binary(b) => b,
            _ => return err,
        };

        if let BinOp::Eq(_tok) = binary.op {
            Ok(Formula::Eq(binary.left, binary.right))
        } else {
            err
        }
    }
}

impl Debug for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Eq(e1, e2) => {
                write!(f, "({} == {})", e1.to_token_stream(), e2.to_token_stream())
            }
        }
    }
}

impl Parse for Formula {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let e: Expr = input.parse()?;
        e.try_into()
    }
}
