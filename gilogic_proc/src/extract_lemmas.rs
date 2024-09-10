use std::collections::HashMap;

use proc_macro::TokenStream as TokenStream_;
use proc_macro2::{Ident, Span};
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
        Ident, // Identifier of `m`
        Token![.],
        kw::extract,
        kw::model,
        Ident, // Identifier of `mp`
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
            lvars.push(LvarDecl::from(model.clone()))
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

            rvars.push(LvarDecl::from((new_model.clone(), new_model_ty)));
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
                tbl.insert(model.to_string(), old_proph_val_var.clone());
                tbl.insert(new_model.to_string(), new_proph_val_var);
                tbl
            };
            prophecise.subst(&subst);

            let subst = {
                let mut tbl = HashMap::new();
                tbl.insert(model.to_string(), old_proph_val_var);
                tbl.insert(new_model.to_string(), new_proph_old_val_var);
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

    let ret_ty: Type = match &item.sig.output {
        ReturnType::Default => parse_quote! { () },
        ReturnType::Type(_token, ty) => (**ty).clone(),
    };

    let ref_ty: Type = match item.sig.inputs.first() {
        Some(arg) => match arg {
            syn::FnArg::Typed(pat) => *pat.ty.clone(),
            _ => {
                return syn::Error::new(arg.span(), "Extract lemma cannot use self")
                    .to_compile_error()
                    .into()
            }
        },
        None => {
            return syn::Error::new(item.sig.span(), "extract lemma needs at least one argument")
                .to_compile_error()
                .into()
        }
    };

    let encoded_el = match extract_lemma.encode(ref_ty, ret_ty.clone()) {
        Ok(stream) => stream,
        Err(error) => return error.to_compile_error().into(),
    };

    let id = uuid::Uuid::new_v4().to_string();
    let name = {
        let ident = item.sig.ident.to_string();
        let name_with_uuid = format!("{}_extract_lemma_{}", ident, id).replace('-', "_");
        format_ident!("{}", name_with_uuid, span = Span::call_site())
    };
    let name_string = name.to_string();

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

    // We need to build the extract lemma term before we add ret to the inputs.
    let extract_lemma_term = quote! {
        #[cfg(gillian)]
        #[rustc_diagnostic_item=#name_string]
        #[gillian::decl::extract_lemma]
        fn #name #generics (#inputs) -> gilogic::RustAssertion {
            // gilogic::__stubs::emp()
            #encoded_el
        }
    };

    inputs.push(parse_quote! { ret : #ret_ty });

    let spec = match extract_lemma
        .make_spec(ret_ty)
        .and_then(|spec| Specification::encode(&spec))
    {
        Ok(stream) => stream,
        Err(error) => return error.to_compile_error().into(),
    };

    let sig = &item.sig;

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
        #[gillian::extract_lemma=#name_string]
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
