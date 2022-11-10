use std::fmt::Debug;

use quote::ToTokens;

use syn::{
    parse::{Parse, ParseStream},
    spanned::Spanned,
    token, BinOp, Error, Expr,
};

pub enum Formula {
    Eq {
        left: Box<Expr>,
        tok: token::EqEq,
        right: Box<Expr>,
    },
}

impl TryFrom<Expr> for Formula {
    type Error = Error;

    fn try_from(value: Expr) -> Result<Self, Self::Error> {
        let err = Err(Error::new(value.span(), "Expr is not a formula"));
        let binary = match value {
            Expr::Binary(b) => b,
            _ => return err,
        };

        if let BinOp::Eq(tok) = binary.op {
            Ok(Formula::Eq {
                left: binary.left,
                tok,
                right: binary.right,
            })
        } else {
            err
        }
    }
}

impl Debug for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Eq { left, right, .. } => {
                write!(
                    f,
                    "({} == {})",
                    left.to_token_stream(),
                    right.to_token_stream()
                )
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
