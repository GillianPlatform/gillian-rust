use std::fmt::Display;
use syn::{parse_quote, spanned::Spanned, Type};

pub fn peel_prophecy_adt<D: Display + Copy>(ty: Type, msg: D) -> syn::Result<Type> {
    let span = ty.span();
    let err = || syn::Error::new(span, msg);
    match ty {
        Type::Paren(typaren) => peel_prophecy_adt(*typaren.elem, msg),
        Type::Path(mut path) => {
            if path.qself.is_some() {
                return Err(err());
            };
            let seg = path.path.segments.pop().ok_or_else(err)?.into_value();
            if seg.ident != "Prophecy" {
                return Err(err());
            }
            let arg = match seg.arguments {
                syn::PathArguments::AngleBracketed(mut args) => {
                    if args.args.len() != 1 {
                        return Err(err());
                    };
                    args.args.pop().ok_or_else(err)?.into_value()
                }
                _ => return Err(err()),
            };
            match arg {
                syn::GenericArgument::Type(ty) => Ok(ty),
                _ => Err(err()),
            }
        }
        _ => Err(err()),
    }
}

pub fn peel_mut_ref<D: Display>(ty: Type, msg: D) -> syn::Result<Type> {
    match ty {
        Type::Paren(typaren) => peel_mut_ref(*typaren.elem, msg),
        Type::Reference(tyref) => {
            if tyref.mutability.is_none() {
                return Err(syn::Error::new(tyref.span(), msg));
            }
            Ok(*tyref.elem)
        }
        _ => Err(syn::Error::new(ty.span(), msg)),
    }
}

pub fn repr_type(ty: &Type) -> Type {
    parse_quote! { <#ty as gilogic::prophecies::Ownable>::RepresentationTy }
}
