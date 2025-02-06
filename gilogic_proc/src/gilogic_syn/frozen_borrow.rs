use proc_macro::TokenStream as TokenStream_;
use proc_macro2::{Span, TokenStream};
use std::collections::HashMap;
use syn::{
    parse::Parse, parse_quote, spanned::Spanned, visit::Visit, visit_mut::VisitMut, FnArg, Ident,
    ImplItem, ItemImpl, PatType, Path, Token, Type,
};

use super::{subst::VarSubst, *};
use crate::visitors::{self, AssertMutator, AssertVisitor};
use quote::{quote, ToTokens};

// Unfortunately, the logic for freezeing borrow is quite different between prophecy-enabled and no-prophecy mode.
// Therefore, have a complete separate implementation. I'm not sure how much can be factored out without much effort.

pub struct FreezeOwnArgs {
    pub lemma_name: Ident,
    pub predicate_name: Ident,
    pub frozen_variables: Vec<Ident>,
    pub resolve_macro_name: Option<Ident>,
}

impl Parse for FreezeOwnArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut lemma_name = None;
        let mut predicate_name = None;
        let mut frozen_variables = None;
        let mut resolve_macro_name = None;
        loop {
            if input.is_empty() {
                break;
            }
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
                "resolve_macro_name" => {
                    resolve_macro_name = Some(input.parse::<Ident>()?);
                }
                _ => {
                    return Err(syn::Error::new(
                        key.span(),
                        "Unknown key in with_freeze_lemma",
                    ));
                }
            };
            if input.peek(syn::Token![,]) {
                let _ = input.parse::<syn::Token![,]>()?;
                continue;
            }
            break;
        }
        let lemma_name = lemma_name
            .ok_or_else(|| syn::Error::new(input.span(), "Missing lemma_name argument"))?;
        let predicate_name = predicate_name
            .ok_or_else(|| syn::Error::new(input.span(), "Missing predicate_name argument"))?;
        let frozen_variables = frozen_variables
            .ok_or_else(|| syn::Error::new(input.span(), "Missing frozen_variables argument"))?
            .into_iter()
            .collect();

        Ok(FreezeOwnArgs {
            lemma_name,
            predicate_name,
            frozen_variables,
            resolve_macro_name,
        })
    }
}

// Declare an assertion mutator that removes all frozen_vars from the existentials and retrieves their type
// while doing so.

struct FreezeMutator<'a> {
    frozen_vars: &'a [Ident],
    frozen_vars_ty: Vec<Type>,
}

impl<'a> AssertMutator for FreezeMutator<'a> {
    fn mutate_assert(&mut self, asrt: &mut Assertion) {
        let mut subst = HashMap::new();
        subst.insert("self".to_string(), Ident::new("THIS", Span::call_site()));
        for frag in asrt.def.iter_mut() {
            frag.subst(&subst);
        }
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

pub struct FreezeOwn {
    pub own_impl: ItemImpl,
    pub predicate: Predicate,
    pub args: FreezeOwnArgs,
    pub prophecy_mode: bool,
}

impl FreezeOwn {
    fn freeze_own(predicate: &mut Predicate, own_impl: &ItemImpl, args: &FreezeOwnArgs) {
        predicate.name = Ident::new("frozen_own".into(), Span::call_site());
        predicate.attributes = vec![];
        predicate.generics = own_impl.generics.clone();

        let mut new_receiver_name = Ident::new("THIS", Span::call_site());
        let mut self_replacer = utils::SelfReplacer {
            replace_with_ty: (*own_impl.self_ty).clone(),
            trait_name: &own_impl.trait_.as_ref().unwrap().1, // We previously checked that this is indeed an impl for Ownable.
        };

        for arg in predicate.args.iter_mut() {
            match arg {
                PredParam::Receiver(_) => {
                    new_receiver_name.set_span(arg.span());
                    let ty = (*own_impl.self_ty).clone();
                    let FnArg::Typed(pat_ty) = parse_quote!(#new_receiver_name : #ty) else {
                        unreachable!()
                    };

                    *arg = PredParam::S(PredParamS {
                        pat_ty,
                        mode: ParamMode::In,
                    })
                }
                PredParam::S(PredParamS {
                    pat_ty: PatType { ty, .. },
                    ..
                }) => self_replacer.visit_type_mut(ty),
            }
        }

        let block = match &mut predicate.body {
            None => panic!("own predicate has no body??"),
            Some(block) => block,
        };
        let mutator = FreezeMutator {
            frozen_vars: &args.frozen_variables,
            frozen_vars_ty: vec![],
        };

        let mut mutator = visitors::AssertMutatorImpl::from(mutator);
        mutator.visit_block_mut(block);

        let frozen_variables = &args.frozen_variables;
        let frozen_vars_ty = mutator.into_inner().frozen_vars_ty;
        let FnArg::Typed(frozen_args) = parse_quote! (
           (#(#frozen_variables,)*) : (#(#frozen_vars_ty,)*)
        ) else {
            unreachable!()
        };
        predicate.args.push(PredParam::S(PredParamS {
            pat_ty: frozen_args,
            mode: ParamMode::Out,
        }));
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
                "with_freeze_lemma should only be applied to Ownable",
            )
        })?;
        if segments.ident != "Ownable" {
            return Err(syn::Error::new(
                path.span(),
                "with_freeze_lemma should only be applied to Ownable",
            ));
        }
        Ok(())
    }

    pub fn parse(args: TokenStream_, input: TokenStream_) -> syn::Result<Self> {
        let args = syn::parse::<FreezeOwnArgs>(args)?;
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
        let prophecy_mode = method.sig.inputs.len() == 2;
        let mut predicate = Predicate::concrete_of_method(method)?;
        Self::freeze_own(&mut predicate, &own_impl, &args);
        // panic!("OBTAINED PREDICATE: {}", predicate.to_token_stream());
        Ok(Self {
            predicate,
            args,
            own_impl,
            prophecy_mode,
        })
    }
}

impl ToTokens for frozen_borrow::FreezeOwn {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let own_impl = &self.own_impl;
        let mut predicate = self.predicate.clone();

        let lemma_name = &self.args.lemma_name;

        // I should store this separately, but no time!!
        let generics = &mut predicate.take_generics();

        let PredParam::S(PredParamS {
            pat_ty: PatType {
                ty: tuple_arg_ty, ..
            },
            ..
        }) = predicate.args.last().unwrap()
        else {
            unreachable!()
        };

        let self_ty = &own_impl.self_ty;

        if let Some(macro_name) = &self.args.resolve_macro_name {
            tokens.extend(quote! {

                fn #macro_name #generics (x : &mut #self_ty) {
                    gilogic::mutref_auto_resolve!(x, #tuple_arg_ty);
                }
            });
        }

        let predicate_name = &self.args.predicate_name;
        generics.params.insert(0, parse_quote! { 'a });

        let module_name = if self.prophecy_mode {
            quote!(gilogic::prophecies)
        } else {
            quote!(gilogic::ownable)
        };

        let predicate_declaration = if self.prophecy_mode {
            quote! {
                #[predicate]
                fn #predicate_name #generics (
                    this: In<&'a mut #self_ty>,
                    model: <&'a mut #self_ty as #module_name::Ownable>::RepresentationTy,
                    frozen: #tuple_arg_ty
                ) {
                    <#self_ty as #module_name::FrozenOwn<#tuple_arg_ty>>::mut_ref_own_frozen(this, model, frozen)
                }
            }
        } else {
            quote! {
                #[predicate]
                fn #predicate_name #generics (
                    this: In<&'a mut #self_ty>,
                    frozen: #tuple_arg_ty
                ) {
                    <#self_ty as #module_name::FrozenOwn<#tuple_arg_ty>>::mut_ref_own_frozen(this, frozen)
                }
            }
        };

        let result = quote! {

            unsafe impl #generics #module_name::FrozenOwn<#tuple_arg_ty> for #self_ty {
                    #predicate
            }

            fn #lemma_name #generics (x: &'a mut #self_ty) {
                #module_name::freeze_params::<#tuple_arg_ty, #self_ty>(x)
            }

            #predicate_declaration

            #own_impl
        };

        tokens.extend(result);
    }
}
