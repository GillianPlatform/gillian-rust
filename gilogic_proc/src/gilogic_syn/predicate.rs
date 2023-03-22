use std::fmt::Debug;

use proc_macro2::Ident;
use quote::ToTokens;
use syn::{
    parse::Parse, punctuated::Punctuated, spanned::Spanned, Attribute, Block, Error, FnArg,
    GenericArgument, Generics, Pat, PatType, PathArguments, Signature, Token, Type, TypePath,
};

#[derive(Debug)]
pub enum ParamMode {
    In,
    Out,
}

pub struct PredParamS {
    pub name: Ident,
    pub colon_token: Token![:],
    pub ty: Type,
    pub mode: ParamMode,
}

pub enum PredParam {
    S(PredParamS),
    Receiver(Token![self]),
}

impl Debug for PredParamS {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#}: ", self.name)?;
        if let ParamMode::In = self.mode {
            write!(f, "+")?;
        }
        write!(f, "{}", self.ty.to_token_stream())?;
        Ok(())
    }
}

impl PredParam {
    /// If the TypePath has form In<T>, returns Some(T),
    /// otherwise returns None
    fn strip_in(tp: &TypePath) -> syn::Result<Option<Type>> {
        let error = |msg| Err(Error::new(tp.span(), msg));

        if tp.qself.is_some() || tp.path.leading_colon.is_some() || tp.path.segments.len() != 1 {
            return Ok(None);
        }

        let segment = tp.path.segments.first().unwrap();
        if &segment.ident.to_string() == "In" {
            match &segment.arguments {
                PathArguments::None => error("`In` used without argument"),
                PathArguments::Parenthesized(..) => error("`In` used with parenthesize arguments"),
                PathArguments::AngleBracketed(abga) => {
                    if abga.colon2_token.is_some() || abga.args.len() != 1 {
                        return error("Invalid arguments for `In`. There should be a single argument without leading double-colon" );
                    }
                    let first = abga.args.first().unwrap();
                    match first {
                        GenericArgument::Type(ty) => Ok(Some(ty.clone())),
                        _ => error("Invalid argument for `In`, it should be a single type"),
                    }
                }
            }
        } else {
            Ok(None)
        }
    }

    fn ident_pat(pat: &Pat) -> syn::Result<Ident> {
        let err = Err(Error::new(
            pat.span(),
            "argument pattern for predicates can only be an identifier with modifier",
        ));
        let patident = match pat {
            Pat::Ident(pat) => pat,
            _ => return err,
        };
        if !patident.attrs.is_empty()
            || patident.by_ref.is_some()
            || patident.mutability.is_some()
            || patident.subpat.is_some()
        {
            return err;
        }
        Ok(patident.ident.clone())
    }

    pub fn is_in(&self) -> bool {
        match self {
            PredParam::S(s) => match s.mode {
                ParamMode::In => true,
                ParamMode::Out => false,
            },
            PredParam::Receiver(_) => true,
        }
    }
}

impl TryFrom<FnArg> for PredParam {
    type Error = syn::Error;

    fn try_from(arg: FnArg) -> syn::Result<Self> {
        match arg {
            FnArg::Receiver(receiver) => {
                if receiver.reference.is_some() || receiver.mutability.is_some() {
                    return Err(Error::new(
                        receiver.span(),
                        "receiver is only allowed to be `self` for predicates",
                    ));
                }
                if !receiver.attrs.is_empty() {
                    return Err(Error::new(
                        receiver.attrs[0].span(),
                        "attributes unsupported for predicate arguments",
                    ));
                }

                Ok(PredParam::Receiver(receiver.self_token))
            }
            FnArg::Typed(PatType {
                attrs,
                pat,
                ty,
                colon_token,
            }) => {
                if !attrs.is_empty() {
                    return Err(Error::new(
                        attrs[0].span(),
                        "attributes unsupported for predicate arguments",
                    ));
                }
                let (ty, mode) = match &*ty {
                    Type::Path(path) => {
                        let stripped_in = Self::strip_in(path)?;
                        match stripped_in {
                            None => ((*ty).clone(), ParamMode::Out),
                            Some(ty) => (ty, ParamMode::In),
                        }
                    }
                    _ => ((*ty).clone(), ParamMode::In),
                };
                let name = Self::ident_pat(&pat)?;
                Ok(PredParam::S(PredParamS {
                    name,
                    ty,
                    mode,
                    colon_token,
                }))
            }
        }
    }
}

pub struct Predicate {
    pub(crate) attributes: Vec<Attribute>,
    pub(crate) name: Ident,
    pub(crate) generics: Generics,
    pub(crate) args: Punctuated<PredParam, Token![,]>,
    pub(crate) body: Option<Block>,
}

fn validate_sig(sig: &Signature) -> syn::Result<()> {
    if let Some(token) = &sig.constness {
        return Err(Error::new(token.span, "const on predicate"));
    }
    if let Some(token) = &sig.asyncness {
        return Err(Error::new(token.span, "async on predicate"));
    }
    if let Some(token) = &sig.unsafety {
        return Err(Error::new(token.span, "unsafe on predicate"));
    }
    if let syn::ReturnType::Type(..) = &sig.output {
        return Err(Error::new(sig.output.span(), "Return type on predicate"));
    }
    if let Some(abi) = &sig.abi {
        return Err(Error::new(abi.span(), "abi for predicate"));
    }
    if let Some(syn::Variadic { dots, .. }) = &sig.variadic {
        return Err(Error::new(dots.span(), "predicate is variadic"));
    }

    Ok(())
}

impl Parse for Predicate {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let attributes = input.call(Attribute::parse_outer)?;
        let sig: Signature = input.parse()?;
        validate_sig(&sig)?;
        let name = sig.ident;
        let args: syn::Result<Punctuated<PredParam, Token![,]>> = sig
            .inputs
            .into_pairs()
            .map(|x| {
                let (arg, comma) = x.into_tuple();
                let arg = PredParam::try_from(arg)?;
                Ok(syn::punctuated::Pair::new(arg, comma))
            })
            .collect();
        let args = args?;
        let generics = sig.generics;
        let body = if input.lookahead1().peek(Token![;]) {
            let _: Token![;] = input.parse().unwrap();
            None
        } else {
            Some(input.parse()?)
        };
        Ok(Predicate {
            name,
            generics,
            args,
            body,
            attributes,
        })
    }
}
