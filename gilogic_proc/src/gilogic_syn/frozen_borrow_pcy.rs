use proc_macro::TokenStream as TokenStream_;
use proc_macro2::Span;
use std::collections::HashMap;
use syn::{
    parse::Parse, parse_quote, spanned::Spanned, visit::Visit, visit_mut::VisitMut, Ident,
    ImplItem, ItemImpl, Path, Token, Type,
};

use super::{subst::VarSubst, *};
use crate::visitors::{self, AssertMutator, AssertVisitor};
use quote::quote;

// Unfortunately, the logic for freezeing borrow is quite different between prophecy-enabled and no-prophecy mode.
// Therefore, have a complete separate implementation. I'm not sure how much can be factored out without much effort.

pub struct FreezeMutRefOwnArgs {
    pub lemma_name: Ident,
    pub predicate_name: Ident,
    pub inner_predicate_name: Ident,
    pub frozen_variables: Vec<Ident>,
}

impl Parse for FreezeMutRefOwnArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut lemma_name = None;
        let mut predicate_name = None;
        let mut frozen_variables = None;
        let mut inner_predicate_name = None;
        for a_count in 0..4 {
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
                        Some(content.parse_terminated::<Ident, syn::Token![,]>(Ident::parse)?);
                }
                "inner_predicate_name" => {
                    inner_predicate_name = Some(input.parse::<Ident>()?);
                }
                _ => {
                    return Err(syn::Error::new(
                        key.span(),
                        "Unknown key in with_freeze_lemma_for_mutref",
                    ));
                }
            };
            if a_count < 3 || input.peek(syn::Token![,]) {
                let _ = input.parse::<syn::Token![,]>()?;
            }
        }
        let lemma_name = lemma_name
            .ok_or_else(|| syn::Error::new(input.span(), "Missing lemma_name argument"))?;
        let predicate_name = predicate_name
            .ok_or_else(|| syn::Error::new(input.span(), "Missing predicate_name argument"))?;
        let inner_predicate_name = inner_predicate_name.ok_or_else(|| {
            syn::Error::new(input.span(), "Missing inner_predicate_name argument")
        })?;
        let frozen_variables = frozen_variables
            .ok_or_else(|| syn::Error::new(input.span(), "Missing frozen_variables argument"))?
            .into_iter()
            .collect();
        Ok(FreezeMutRefOwnArgs {
            lemma_name,
            predicate_name,
            frozen_variables,
            inner_predicate_name,
        })
    }
}

// Declare an assertion mutator that:
// 1) Removes the required variables and their types from existentials, and adds them to the parameters.
// 2) Replaces the receiver with a mutable reference to the receiver (with another name).
// 3) Creates an existential to the old receiver and adds SELF -> old_receiver to the assertion.

struct FreezeMutator<'a> {
    frozen_vars: &'a [Ident],
    frozen_vars_ty: Vec<Type>,
    own_impl_ty: &'a Type,
    model: (Ident, Type),
}

impl<'a> AssertMutator for FreezeMutator<'a> {
    fn mutate_assert(&mut self, asrt: &mut Assertion) {
        let mut subst = HashMap::new();
        subst.insert("self".to_string(), Ident::new("SELF", Span::call_site()));
        for frag in asrt.def.iter_mut() {
            frag.subst(&subst);
        }
        let model_name = &self.model.0;
        let points_to = syn::parse2::<AsrtFragment>(quote::quote! { (REFERENCE -> SELF) }).unwrap();
        let controller = syn::parse2::<AsrtFragment>(
            quote::quote! { gilogic::prophecies::controller(REFERENCE.prophecy(), #model_name) },
        )
        .unwrap();
        asrt.def.push(points_to);
        asrt.def.push(controller);
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
        asrt.lvars.push(LvarDecl {
            ident: self.model.0.clone(),
            ty_opt: Some((Token![:](self.model.0.span()), self.model.1.clone())),
        })
    }
}

struct FreezeVisitor<'a> {
    frozen_vars: &'a [Ident],
    frozen_vars_ty: Vec<Type>,
}

// When not mutating, it just accumulates the lvars types that need to be frozen
impl<'ast> AssertVisitor for FreezeVisitor<'ast> {
    fn visit_assert(&mut self, asrt: &Assertion) {
        for decl in &asrt.lvars {
            if self.frozen_vars.contains(&decl.ident) {
                self.frozen_vars_ty.push(
                    decl.ty_opt
                        .as_ref()
                        .unwrap_or_else(|| {
                            panic!(
                                "Existential variable {} needs explicit typing to be frozen",
                                decl.ident
                            )
                        })
                        .1
                        .clone(),
                );
            }
        }
    }
}

pub struct FreezeMutRefOwn {
    pub own_impl: ItemImpl,
    pub predicate: Predicate,
    pub inner_predicate: Predicate,
    pub args: FreezeMutRefOwnArgs,
}

impl FreezeMutRefOwn {
    fn freeze_inner(predicate: &mut Predicate, own_impl: &ItemImpl, args: &FreezeMutRefOwnArgs) {
        predicate.name = args.inner_predicate_name.clone();
        predicate.attributes = vec![];
        predicate.generics = own_impl.generics.clone();

        let mut new_receiver_name = Ident::new("REFERENCE", Span::call_site());
        let self_mut_ref = {
            let self_ty = (*own_impl.self_ty).clone();
            syn::parse2::<Type>(quote::quote!(&mut #self_ty)).unwrap()
        };
        let mut self_replacer = utils::SelfReplacer {
            replace_with_ty: (*own_impl.self_ty).clone(),
            trait_name: &own_impl.trait_.as_ref().unwrap().1, // We previously checked that this is indeed an impl for Ownable.
        };
        let PredParam::S(PredParamS {
            name: model_name,
            ty: mut model_ty,
            ..
        }) = predicate.args.pop().unwrap().into_value()
        else {
            panic!("model doesn't exist???")
        }; // we remove the model parameter here.
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
        self_replacer.visit_type_mut(&mut model_ty);
        let mutator = FreezeMutator {
            frozen_vars: &args.frozen_variables,
            frozen_vars_ty: vec![],
            own_impl_ty: &own_impl.self_ty,
            model: (model_name, model_ty),
        };
        let mut mutator = visitors::AssertMutatorImpl::from(mutator);
        mutator.visit_block_mut(block);
        let frozen_args = args
            .frozen_variables
            .iter()
            .zip(mutator.into_inner().frozen_vars_ty);
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

    fn freeze_outer(predicate: &mut Predicate, own_impl: &ItemImpl, args: &FreezeMutRefOwnArgs) {
        let name = &args.predicate_name;
        predicate.generics = own_impl.generics.clone();
        predicate.generics.params.insert(0, parse_quote! { 'gil });

        let generics = &predicate.generics;
        let inner_pred_name = &args.inner_predicate_name;
        let frozen_vars = &args.frozen_variables;
        let impl_ty = (*own_impl.self_ty).clone();
        let mut visitor = visitors::AssertVisitorImpl::from(FreezeVisitor {
            frozen_vars,
            frozen_vars_ty: vec![],
        });
        visitor.visit_block(predicate.body.as_ref().unwrap());
        let frozen_vars_ty = visitor.into_inner().frozen_vars_ty;
        let outer = quote! {
            fn #name #generics (REFERENCE: In<&'gil mut #impl_ty>, model: (<&'gil mut #impl_ty as Ownable>::RepresentationTy), #(#frozen_vars: #frozen_vars_ty),*) {
                assertion!(|current: <#impl_ty as Ownable>::RepresentationTy|
                    (model == (current, REFERENCE.prophecy().value())) *
                    gilogic::prophecies::observer(REFERENCE.prophecy(), current) *
                    #inner_pred_name(REFERENCE, #(#frozen_vars),*)
                )
            }
        };
        let new_predicate = syn::parse2::<Predicate>(outer).unwrap();
        *predicate = new_predicate;
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
                ImplItem::Method(method) if method.sig.ident == "own" => Some(method.clone()),
                _ => None,
            })
            .ok_or_else(|| syn::Error::new(own_impl.span(), "No own method found"))?;
        let mut predicate = Predicate::concrete_of_method(method)?;
        let mut inner_predicate = predicate.clone();
        Self::freeze_inner(&mut inner_predicate, &own_impl, &args);
        Self::freeze_outer(&mut predicate, &own_impl, &args);
        Ok(Self {
            inner_predicate,
            predicate,
            args,
            own_impl,
        })
    }
}
