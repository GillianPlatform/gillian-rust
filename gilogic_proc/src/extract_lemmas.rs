use std::collections::HashMap;

use proc_macro::TokenStream as TokenStream_;
use proc_macro2::Span;
use syn::{
    braced, parse::Parse, parse_macro_input, parse_quote, punctuated::Punctuated, spanned::Spanned,
    ReturnType, Token, TraitItemFn, Type,
};

use quote::{format_ident, quote};

use crate::{
    kw, subst::VarSubst, AsrtFragment, AsrtPredCall, Formula, LvarDecl, Observation, SpecEnsures,
    Specification, Term,
};

pub struct ExtractLemma {
    // forall x, y.
    pub forall: Option<(kw::forall, Punctuated<LvarDecl, Token![,]>, Token![.])>,
    // model m.
    // new model mp.
    pub models: Option<(
        kw::model,
        LvarDecl, // Identifier of `m`
        Token![.],
        kw::extract,
        kw::model,
        LvarDecl, // Identifier of `mp`
        Token![.],
    )>,
    // assuming { F }
    pub assuming: Option<(kw::assuming, Term)>,
    // from { borrow }
    pub from: (kw::from, AsrtPredCall),
    pub extract: (kw::extract, AsrtPredCall),
    pub prophecise: Option<(kw::prophecise, Term)>,
}

impl ExtractLemma {
    fn make_spec(&self, ret_ty: Type) -> syn::Result<Specification> {
        let (forall, mut lvars, dot) = match &self.forall {
            Some((token, lvars, dot)) => (Some(*token), lvars.clone(), Some(*dot)),
            None => (None, Punctuated::new(), None),
        };
        if let Some((_, model, _, _, _, _, _)) = &self.models {
            lvars.push(model.clone())
        };
        let (_, from_borrow) = &self.from;
        let from_borrow: AsrtPredCall = from_borrow.clone();

        let precond = {
            let mut precond = Punctuated::new();
            precond.push(AsrtFragment::PredCall(from_borrow));
            if let Some((_, term)) = &self.assuming {
                let term = term.clone();
                let f = AsrtFragment::Pure(Formula {
                    paren_token: Default::default(),
                    inner: term,
                });
                precond.push(f);
            };
            precond
        };
        let mut rvars = Punctuated::new();
        let mut postcond = Punctuated::new();
        let (_, extract) = &self.extract;
        // Don't know how to clone otherwise
        let mut extract: AsrtPredCall = extract.clone();
        let mut dot2 = None;
        // If there is a model, we create new prophecy variable and put it and
        // the new model as existentials for the post.
        // We also add the .with_prophecy(_PROPH) to the pointer passed as first parameter of extracted.
        if let Some((model_kw, model, _, _, _, new_model, dot)) = self.models.clone() {
            dot2 = Some(dot);

            let prophecy_ty = super::utils::peel_prophecy_adt(
                ret_ty,
                "extract_lemma must return Prophecy<K> for some K when used with prophecies",
            )?;
            let new_model_ty: Type = parse_quote! { (#prophecy_ty, #prophecy_ty) };
            // panic!("{new_model:?}");

            rvars.push(LvarDecl::from((new_model.ident.clone(), new_model_ty)));
            let fresh_prophecy = format_ident!("ret");
            let extract_span = extract.span();
            let ptr_arg_extracted_mut = extract.args_mut().first_mut().ok_or_else(|| {
                syn::Error::new(extract_span, "Extracting a borrow with no arguments?")
            })?;

            let ptr_arg_extracted = ptr_arg_extracted_mut.clone();
            *ptr_arg_extracted_mut =
                syn::parse2(quote!(gilogic::prophecies::Prophecised::with_prophecy(#ptr_arg_extracted, #fresh_prophecy))).unwrap();

            let old_proph_val_var = format_ident!("__OLD_PROPH_VAL");
            let new_proph_val_var = format_ident!("__NEW_PROPH_VAL");
            let new_proph_old_val_var = format_ident!("__NEW_PROPH_OLD_VAL");
            rvars.push(LvarDecl::from(old_proph_val_var.clone()));
            rvars.push(LvarDecl::from(new_proph_val_var.clone()));
            rvars.push(LvarDecl::from(new_proph_old_val_var.clone()));
            let old_proph_eq = {
                let term = parse_quote!(
                    #old_proph_val_var == #model.0
                );
                AsrtFragment::Pure(Formula::from_term(term))
            };

            let new_proph_eq = {
                let term = parse_quote!(
                    #new_proph_val_var == #new_model.1
                );
                AsrtFragment::Pure(Formula::from_term(term))
            };

            let new_proph_old_eq = {
                let term = parse_quote!(
                    #new_proph_old_val_var == #new_model.0
                );
                AsrtFragment::Pure(Formula::from_term(term))
            };

            let (_, prophecise) = self.prophecise.as_ref().ok_or_else(|| {
                syn::Error::new(
                    model_kw.span(),
                    "Cannot specify model without specifying how it is prophecised",
                )
            })?;
            let mut prophecise = prophecise.clone();
            let mut prophecise_past = prophecise.clone();

            postcond.push(old_proph_eq);
            postcond.push(new_proph_eq);
            postcond.push(new_proph_old_eq);

            let subst = {
                let mut tbl = HashMap::new();
                tbl.insert(model.ident.to_string(), old_proph_val_var.clone());
                tbl.insert(new_model.ident.to_string(), new_proph_val_var);
                tbl
            };
            prophecise.subst(&subst);

            let subst = {
                let mut tbl = HashMap::new();
                tbl.insert(model.ident.to_string(), old_proph_val_var);
                tbl.insert(new_model.ident.to_string(), new_proph_old_val_var);
                tbl
            };
            prophecise_past.subst(&subst);

            let inner = parse_quote!(
                (#model.1 == (#prophecise)) &&
                (#model.0 == (#prophecise_past))
            );

            let observation = AsrtFragment::Observation(Observation {
                open_dollar: Default::default(),
                inner,
                close_dollar: Default::default(),
            });
            postcond.push(observation);
        }
        postcond.push(AsrtFragment::PredCall(extract));

        let ensures = SpecEnsures {
            exists: if rvars.is_empty() {
                None
            } else {
                Some(kw::exists(Span::call_site()))
            },
            rvars,
            dot2,
            ensures: kw::ensures(Span::call_site()),
            postcond,
        };

        Ok(Specification {
            forall,
            lvars,
            dot,
            requires: kw::requires(Span::call_site()),
            precond,
            postconds: vec![ensures],
        })
    }
}

impl Parse for ExtractLemma {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let forall = if input.lookahead1().peek(kw::forall) {
            let forall = input.parse::<kw::forall>()?;
            let lvars = Punctuated::parse_separated_nonempty(input)?;
            let dot = input.parse()?;
            Some((forall, lvars, dot))
        } else {
            None
        };

        let models = if input.lookahead1().peek(kw::model) {
            let model = input.parse::<kw::model>()?;
            let lvar = input.parse()?;
            let dot = input.parse()?;
            let new_ = input.parse()?;
            let new_model = input.parse()?;
            let new_lvar = input.parse()?;
            let new_dot = input.parse()?;
            Some((model, lvar, dot, new_, new_model, new_lvar, new_dot))
        } else {
            None
        };

        let assuming = if input.lookahead1().peek(kw::assuming) {
            let assuming = input.parse::<kw::assuming>()?;
            let content;
            let _ = braced!(content in input);
            let term = content.parse()?;
            Some((assuming, term))
        } else {
            None
        };

        let from = {
            let tok = input.parse::<kw::from>()?;
            let content;
            let _ = braced!(content in input);
            let call = content.parse()?;
            (tok, call)
        };
        let extract = {
            let tok = input.parse::<kw::extract>()?;
            let content;
            let _ = braced!(content in input);
            let call = content.parse()?;
            (tok, call)
        };

        let prophecise = if input.lookahead1().peek(kw::prophecise) {
            let prophecise = input.parse::<kw::prophecise>()?;
            let content;
            let _ = braced!(content in input);
            let term = content.parse()?;
            Some((prophecise, term))
        } else {
            None
        };
        if (prophecise.is_some() && models.is_none()) || (prophecise.is_none() && models.is_some())
        {
            return Err(syn::Error::new(
                input.cursor().span(),
                format!(
                    "Must either specify both models and prophecise or neither: {}.",
                    input
                ),
            ));
        }

        Ok(ExtractLemma {
            forall,
            models,
            assuming,
            from,
            extract,
            prophecise,
        })
    }
}

pub(crate) fn extract_lemma(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    let mut item = parse_macro_input!(input as TraitItemFn);
    let item_attrs = std::mem::take(&mut item.attrs);
    let extract_lemma = parse_macro_input!(args as ExtractLemma);

    let is_trusted = item_attrs.iter().any(|attr| {
        attr.path().is_ident("trusted")
            || (attr.path().segments.len() == 2
                && attr.path().segments[0].ident == "gillian"
                && attr.path().segments[1].ident == "trusted")
    });

    let ret_ty: Type = match &item.sig.output {
        ReturnType::Default => parse_quote! { () },
        ReturnType::Type(_token, ty) => (**ty).clone(),
    };

    let spec_id = uuid::Uuid::new_v4().to_string();
    let spec_name = {
        let ident = item.sig.ident.to_string();
        let name_with_uuid = format!("{}_spec_{}", ident, spec_id).replace('-', "_");
        format_ident!("{}", name_with_uuid, span = Span::call_site())
    };
    let spec_name_string = spec_name.to_string();
    let ins = format!("{}", item.sig.inputs.len());

    let mut inputs = item.sig.inputs.clone();
    let generics = &item.sig.generics;

    inputs.push(parse_quote! { ret : #ret_ty });

    let spec = match extract_lemma
        .make_spec(ret_ty)
        .and_then(|spec| Specification::encode(&spec))
    {
        Ok(stream) => stream,
        Err(error) => return error.to_compile_error().into(),
    };

    let sig = &item.sig;

    let extract_lemma_term = if is_trusted {
        None
    } else if extract_lemma.prophecise.is_some() {
        Some(extract_lemma_term_proph(&extract_lemma, &item))
    } else {
        Some(extract_lemma_noproph(&extract_lemma, &item))
    };

    let result = quote! {
        #extract_lemma_term

        #[cfg(gillian)]
        #[rustc_diagnostic_item=#spec_name_string]
        #[gillian::decl::specification]
        #[gillian::decl::pred_ins=#ins]
        fn #spec_name #generics (#inputs) -> gilogic::RustAssertion {
            #spec
        }

        #(#item_attrs)*
        #[gillian::spec=#spec_name_string]
        #[allow(unsused_variables)]
        #[gillian::trusted]
        #sig {
            unreachable!()
        }
    };

    // panic!("{:?}", result.to_string());

    result.into()
}

pub(crate) fn extract_lemma_term_proph(
    extract_lemma: &ExtractLemma,
    item: &TraitItemFn,
) -> proc_macro2::TokenStream {
    let name = item.sig.ident.clone();
    let inputs = item.sig.inputs.clone();
    let generics = &item.sig.generics;

    // We need to build the extract lemma term before we add ret to the inputs.
    let extract_lemma_term = {
        let proof_name = format_ident!("{}___proof", name);
        let from_args = extract_lemma.from.1.args().clone();

        let mut extract_args = extract_lemma.extract.1.args().clone();
        if extract_args.len() < 3 {
            // It's an own predicate and not a frozen own predicate, we add the unit parameter.
            extract_args.push(parse_quote!(()));
        }

        let new_new_model = format_ident!("new_new_model");
        // let new_model = extract_args[1].clone();

        let mut wand_pre_args = extract_args.clone();
        wand_pre_args[1] = parse_quote! { #new_new_model };

        let assuming = if let Some((_, term)) = &extract_lemma.assuming {
            Some(quote! { (#term) * })
        } else {
            None
        };

        let (_, term) = &extract_lemma
            .prophecise
            .as_ref()
            .expect("need prophecise to be set");

        let (_, model, _, _, _, _new_model, _) = extract_lemma
            .models
            .as_ref()
            .expect("need models to be set");
        let prophecise_check = Some(quote! { * (#model == #term) });

        let mut subst = HashMap::new();
        subst.insert(_new_model.ident.to_string(), new_new_model.clone());
        let mut wand_proph = term.clone();
        wand_proph.subst(&subst);
        let mut wand_post_args = from_args.clone();
        wand_post_args[1] = wand_proph;

        let forall = if let Some((forall, lvars, dot)) = &extract_lemma.forall {
            let mut lvars = lvars.clone();
            if let Some((_, model, _, _, _, _, _)) = &extract_lemma.models {
                lvars.push(model.clone());
            }
            lvars.push(parse_quote! { #new_new_model});

            // HACK: inputs is not properly interpolated here
            let forall = quote! { #forall #inputs, #lvars #dot };
            Some(forall)
        } else {
            Some(quote! { forall #new_new_model .})
        };

        let exists = if let Some((_, _, _, _, _, new_model, _)) = &extract_lemma.models {
            Some(quote! { exists #new_model . })
        } else {
            None
        };

        quote! {
            #[gilogic::macros::lemma]
            #[gilogic::macros::specification(
                    #forall
                    requires {
                        #assuming
                        gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(#from_args)
                    }
                    #exists
                    ensures {
                        gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(#extract_args)
                        #prophecise_check
                        * gilogic::__stubs::wand(
                            gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(#wand_pre_args),
                            gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(#wand_post_args)
                        )
                    }
            )]
            #[gillian::args_deferred]
            #[gillian::timeless]
            fn #proof_name #generics (#inputs) {
                ::gilogic :: package!(
                  gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(#wand_pre_args)
                , gilogic::prophecies::FrozenOwn::just_ref_mut_points_to(#wand_post_args)
                );
            }
        }
    };

    extract_lemma_term
}

pub(crate) fn extract_lemma_noproph(
    extract_lemma: &ExtractLemma,
    item: &TraitItemFn,
) -> proc_macro2::TokenStream {
    let name = item.sig.ident.clone();
    let inputs = item.sig.inputs.clone();
    let generics = &item.sig.generics;

    // We need to build the extract lemma term before we add ret to the inputs.
    let extract_lemma_term = {
        let proof_name = format_ident!("{}___proof", name);
        let from_args = extract_lemma.from.1.args().clone();

        let mut extract_args = extract_lemma.extract.1.args().clone();
        if extract_args.len() < 3 {
            // It's an own predicate and not a frozen own predicate, we add the unit parameter.
            extract_args.push(parse_quote!(()));
        }

        // let new_model = extract_args[1].clone();

        let wand_pre_args = extract_args.clone();

        let assuming = if let Some((_, term)) = &extract_lemma.assuming {
            Some(quote! { (#term) * })
        } else {
            None
        };

        let wand_post_args = from_args.clone();

        let forall = if let Some((forall, lvars, dot)) = &extract_lemma.forall {
            let mut lvars = lvars.clone();
            if let Some((_, model, _, _, _, _, _)) = &extract_lemma.models {
                lvars.push(model.clone());
            }

            // HACK: inputs is not properly interpolated here
            let forall = quote! { #forall #inputs, #lvars #dot };
            Some(forall)
        } else {
            None
        };

        let exists = if let Some((_, _, _, _, _, new_model, _)) = &extract_lemma.models {
            Some(quote! { exists #new_model . })
        } else {
            None
        };

        quote! {
            #[gilogic::macros::lemma]
            #[gilogic::macros::specification(
                    #forall
                    requires {
                        #assuming
                        gilogic::ownable::FrozenOwn::just_ref_mut_points_to(#from_args)
                    }
                    #exists
                    ensures {
                        gilogic::ownable::FrozenOwn::just_ref_mut_points_to(#extract_args)
                        * gilogic::__stubs::wand(
                            gilogic::ownable::FrozenOwn::just_ref_mut_points_to(#wand_pre_args),
                            gilogic::ownable::FrozenOwn::just_ref_mut_points_to(#wand_post_args)
                        )
                    }
            )]
            #[gillian::args_deferred]
            #[gillian::timeless]
            fn #proof_name #generics (#inputs) {
                    ::gilogic :: package!(
                      gilogic::ownable::FrozenOwn::just_ref_mut_points_to(#wand_pre_args)
                    , gilogic::ownable::FrozenOwn::just_ref_mut_points_to(#wand_post_args)
                    );
            }
        }
    };

    extract_lemma_term
}
