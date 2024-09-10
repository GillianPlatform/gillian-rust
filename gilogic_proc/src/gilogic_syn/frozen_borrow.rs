use std::collections::HashMap;

use proc_macro::TokenStream as TokenStream_;
use proc_macro2::Span;
use syn::{
    parse::Parse, spanned::Spanned, visit_mut::VisitMut, Ident, ImplItem, ItemImpl, Path, Token,
    Type,
};

use crate::visitors::{self, AssertMutator};

use super::{subst::VarSubst, utils::SelfReplacer, *};

pub struct FreezeMutRefOwnArgs {
    pub lemma_name: Ident,
    pub predicate_name: Ident,
    pub frozen_variables: Vec<Ident>,
}

impl Parse for FreezeMutRefOwnArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut lemma_name = None;
        let mut predicate_name = None;
        let mut frozen_variables = None;
        for a_count in 0..3 {
            let key = input.parse::<Ident>()?;
            let _ = input.parse::<syn::Token![=]>()?;
            match key.to_string().as_str() {
                "lemma_name" => {
                    lemma_name = Some(input.parse::<Ident>()?);
                }
                "predicate_name" => {
                    predicate_name = Some(input.parse::<Ident>()?);
                }
                "frozen_variables" => {
                    let content;
                    syn::bracketed!(content in input);
                    frozen_variables =
                        Some(content.parse_terminated::<Ident, _>(Ident::parse, Token![,])?);
                }
                _ => {
                    return Err(syn::Error::new(
                        key.span(),
                        "Unknown key in with_freeze_lemma_for_mutref",
                    ));
                }
            };
            if a_count < 2 || input.peek(syn::Token![,]) {
                let _ = input.parse::<syn::Token![,]>()?;
            }
        }
        let lemma_name = lemma_name
            .ok_or_else(|| syn::Error::new(input.span(), "Missing lemma_name argument"))?;
        let predicate_name = predicate_name
            .ok_or_else(|| syn::Error::new(input.span(), "Missing predicate_name argument"))?;
        let frozen_variables = frozen_variables
            .ok_or_else(|| syn::Error::new(input.span(), "Missing frozen_variables argument"))?
            .into_iter()
            .collect();

        Ok(FreezeMutRefOwnArgs {
            lemma_name,
            predicate_name,
            frozen_variables,
        })
    }
}

// Declare an assertion mutator that:
// 1) Removes the required variables and their types from existentials, and adds them to the parameters.
// 2) Replaces the receiver with a mutable reference to the receiver (with another name).
// 3) Creates an existential to the old receiver and adds SELF -> old_receiver to the assertion.

struct Mutator<'a> {
    frozen_vars: &'a [Ident],
    frozen_vars_ty: Vec<Type>,
    own_impl_ty: &'a Type,
}

impl<'a> AssertMutator for Mutator<'a> {
    fn mutate_assert(&mut self, asrt: &mut Assertion) {
        let mut subst = HashMap::new();
        subst.insert("self".to_string(), Ident::new("SELF", Span::call_site()));
        for frag in asrt.def.iter_mut() {
            frag.subst(&subst);
        }
        let points_to = syn::parse2::<AsrtFragment>(quote::quote! { (REFERENCE -> SELF) }).unwrap();
        asrt.def.push(points_to);
        let lvars = std::mem::take(&mut asrt.lvars);
        asrt.lvars = lvars
            .into_pairs()
            .filter(|pair| {
                let lvar = pair.value();
                if self.frozen_vars.contains(&lvar.ident) {
                    self.frozen_vars_ty.push(
                        lvar.ty_opt
                            .as_ref()
                            .unwrap_or_else(|| {
                                panic!(
                                    "Existential variable {} needs explicit typing to be frozen",
                                    lvar.ident
                                )
                            })
                            .1
                            .clone(),
                    );
                    false
                } else {
                    true
                }
            })
            .collect();
        asrt.lvars.push(LvarDecl {
            ident: Ident::new("SELF", Span::call_site()),
            ty_opt: Some((syn::Token![:](Span::call_site()), self.own_impl_ty.clone())),
        });
    }
}

pub struct FreezeMutRefOwn {
    pub own_impl: ItemImpl,
    pub predicate: Predicate,
    pub args: FreezeMutRefOwnArgs,
}

impl FreezeMutRefOwn {
    fn freeze(predicate: &mut Predicate, own_impl: &ItemImpl, args: &FreezeMutRefOwnArgs) {
        predicate.name = args.predicate_name.clone();
        predicate.attributes = vec![];
        predicate.generics = own_impl.generics.clone();
        let mut new_receiver_name = Ident::new("REFERENCE", Span::call_site());
        let self_mut_ref = {
            let self_ty = (*own_impl.self_ty).clone();
            syn::parse2::<Type>(quote::quote!(&mut #self_ty)).unwrap()
        };
        let mut self_replacer = SelfReplacer {
            replace_with_ty: (*own_impl.self_ty).clone(),
            trait_name: &own_impl.trait_.as_ref().unwrap().1, // We previously checked that this is indeed an impl for Ownable.
        };
        for arg in predicate.args.iter_mut() {
            match arg {
                PredParam::Receiver(_) => {
                    new_receiver_name.set_span(arg.span());
                    *arg = PredParam::S(PredParamS {
                        name: new_receiver_name.clone(),
                        ty: self_mut_ref.clone(),
                        mode: ParamMode::In,
                        colon_token: syn::Token![:](arg.span()),
                    })
                }
                PredParam::S(PredParamS { ty, .. }) => self_replacer.visit_type_mut(ty),
            }
        }
        let block = match &mut predicate.body {
            None => panic!("own predicate has no body??"),
            Some(block) => block,
        };
        let mutator = Mutator {
            frozen_vars: &args.frozen_variables,
            frozen_vars_ty: vec![],
            own_impl_ty: &own_impl.self_ty,
        };

        let mut mutator = visitors::AssertMutatorImpl::from(mutator);
        mutator.visit_block_mut(block);

        let frozen_args: Vec<_> = args
            .frozen_variables
            .iter()
            .zip(mutator.into_inner().frozen_vars_ty)
            .collect();

        for (ident, ty) in frozen_args {
            let pred_param = PredParam::S(PredParamS {
                name: ident.clone(),
                colon_token: Token![:](ident.span()),
                ty,
                mode: ParamMode::Out,
            });
            predicate.args.push(pred_param);
        }
    }

    fn check_trait_is_ownable(
        path: &Option<(Option<Token![!]>, Path, Token![for])>,
        span: Span,
    ) -> syn::Result<()> {
        let (bang, path, _) = path
            .as_ref()
            .ok_or_else(|| syn::Error::new(span, "Not ownable trait?"))?;
        if !bang.is_none() {
            return Err(syn::Error::new(span, "Not ownable trait?"));
        }
        let segments = path.segments.last().ok_or_else(|| {
            syn::Error::new(
                path.span(),
                "with_freeze_lemma_for_mutref should only be applied to Ownable",
            )
        })?;
        if segments.ident != "Ownable" {
            return Err(syn::Error::new(
                path.span(),
                "with_freeze_lemma_for_mutref should only be applied to Ownable",
            ));
        }
        Ok(())
    }

    pub fn parse(args: TokenStream_, input: TokenStream_) -> syn::Result<Self> {
        let args = syn::parse::<FreezeMutRefOwnArgs>(args)?;
        let own_impl = syn::parse::<ItemImpl>(input)?;
        Self::check_trait_is_ownable(&own_impl.trait_, own_impl.span())?;
        let method = own_impl
            .items
            .iter()
            .find_map(|item| match item {
                ImplItem::Fn(method) if method.sig.ident == "own" => Some(method.clone()),
                _ => None,
            })
            .ok_or_else(|| syn::Error::new(own_impl.span(), "No own method found"))?;
        let mut predicate = Predicate::concrete_of_method(method)?;
        Self::freeze(&mut predicate, &own_impl, &args);
        Ok(Self {
            predicate,
            args,
            own_impl,
        })
    }
}
