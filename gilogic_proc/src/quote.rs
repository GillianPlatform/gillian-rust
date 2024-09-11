use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, quote_spanned, ToTokens};
use syn::{
    parse_quote, spanned::Spanned, BinOp, Error, Lit, LitBool, PatType, Stmt, StmtMacro, Type,
};
use uuid::Uuid;

use crate::{extract_lemmas::ExtractLemma, gilogic_syn::*, spec::compile_spec};

impl Formula {
    fn encode_inner(inner: &Term) -> syn::Result<TokenStream> {
        let mut tokens = TokenStream::new();
        match inner {
            Term::Binary(TermBinary { left, op, right }) => match op {
                BinOp::Eq(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                      gilogic::__stubs::equal(#left, #right)
                    ));
                }
                BinOp::Le(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                      gilogic::__stubs::less_eq(#left, #right)
                    ));
                }
                BinOp::Lt(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                      gilogic::__stubs::less(#left, #right)
                    ));
                }
                BinOp::Gt(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                      gilogic::__stubs::less(#right, #left)
                    ));
                }
                BinOp::Ge(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                        gilogic::__stubs::less(#right, #left)
                    ));
                }
                BinOp::And(tok) => {
                    let span = tok.span();
                    let left = Self::encode_inner(left)?;
                    let right = Self::encode_inner(right)?;
                    tokens.extend(quote_spanned!(span=>
                        gilogic::__stubs::and(#left, #right)
                    ));
                }
                BinOp::Or(tok) => {
                    let span = tok.span();
                    let left = Self::encode_inner(left)?;
                    let right = Self::encode_inner(right)?;
                    tokens.extend(quote_spanned!(span=>
                        gilogic::__stubs::or(#left, #right)
                    ));
                }
                BinOp::Ne(tok) => {
                    let span = tok.span();
                    tokens.extend(quote_spanned!(span=>
                        gilogic::__stubs::not_equal(#left, #right)
                    ));
                }
                _ => {
                    return Err(Error::new(
                        op.span(),
                        "Unsupported binary operator for formula",
                    ))
                }
            },
            Term::Paren(TermParen {
                paren_token: _,
                expr,
            }) => {
                let inner = Self::encode_inner(expr)?;
                tokens.extend(inner);
            }
            Term::Forall(TermForall {
                forall_token: _,
                lt_token: _,
                args,
                gt_token: _,
                term,
            }) => {
                let mut ts = Self::encode_inner(term)?;
                for arg in args {
                    ts = quote! {
                        gilogic::__stubs::forall(
                            #[gillian::no_translate]
                            |#arg| { #ts }
                        )
                    }
                }
                tokens.extend(ts)
            }
            Term::Exists(TermExists {
                exists_token: _,
                lt_token: _,
                args,
                gt_token: _,
                term,
            }) => {
                let mut ts = encode_expr(term)?;
                for arg in args {
                    ts = quote! {
                        gilogic::__stubs::exists(
                            #[gillian::no_translate]
                            (|#arg| #ts)
                        )
                    }
                }
                tokens.extend(ts)
            }
            Term::Impl(TermImpl {
                hyp,
                eqeq_token: _,
                gt_token: _,
                cons,
            }) => {
                let span = inner.span();
                let hyp = Self::encode_inner(hyp)?;
                let cons = Self::encode_inner(cons)?;
                tokens.extend(quote_spanned! {span=>
                    gilogic::__stubs::implication(#hyp, #cons)
                });
            }
            Term::Path(p) => tokens.extend(quote!(
              gilogic::__stubs::equal(#p, true)
            )),
            Term::Lit(l) => tokens.extend(quote! { #l }),
            e => {
                return Err(Error::new(
                    inner.span(),
                    format!("Expression is not a supported formula {e:?}"),
                ))
            }
        }
        Ok(tokens)
    }

    pub fn encode(&self) -> syn::Result<TokenStream> {
        Self::encode_inner(&self.inner)
    }
}

fn encode_expr(inner: &Term) -> syn::Result<TokenStream> {
    let mut tokens = TokenStream::new();
    match inner {
        Term::Binary(TermBinary { left, op, right }) => {
            let l = encode_expr(left)?;
            let r = encode_expr(right)?;
            match op {
                BinOp::Eq(_) => tokens.extend(quote! { gilogic :: __stubs :: expr_eq (#l, #r) }),
                BinOp::Ne(_) => tokens.extend(quote! { gilogic :: __stubs :: expr_ne (#l, #r) }),
                _ => tokens.extend(quote! { #l #op #r }),
            }
        }
        // Term::Block(_) => todo!(),
        Term::Call(TermCall { func, args, .. }) => {
            let args: Vec<_> = args
                .iter()
                .map(|f| encode_expr(&f))
                .collect::<syn::Result<_>>()?;
            tokens.extend(quote! { #func ( #(#args),* ) })
        }
        Term::Field(TermField {
            base,
            dot_token: _,
            member,
        }) => {
            let base = encode_expr(base)?;

            tokens.extend(quote! { #base . #member })
        }
        Term::Impl(TermImpl {
            hyp,
            eqeq_token: _,
            gt_token: _,
            cons,
        }) => {
            let span = inner.span();
            let hyp = encode_expr(hyp)?;
            let cons = encode_expr(cons)?;
            tokens.extend(quote_spanned! {span=>
                gilogic::__stubs::expr_implies(#hyp, #cons)
            });
        }
        Term::Exists(TermExists {
            exists_token: _,
            lt_token: _,
            args,
            gt_token: _,
            term,
        }) => {
            let mut ts = encode_expr(term)?;
            for arg in args {
                ts = quote! {
                    gilogic::__stubs::exists(
                        #[gillian::no_translate]
                        (|#arg| #ts)
                    )
                }
            }
            tokens.extend(ts)
        }
        Term::Forall(TermForall {
            forall_token: _,
            lt_token: _,
            args,
            gt_token: _,
            term,
        }) => {
            let mut ts = encode_expr(term)?;
            for arg in args {
                ts = quote! {
                    gilogic::__stubs::eforall(
                        #[gillian::no_translate]
                        (|#arg| #ts)
                    )
                }
            }
            tokens.extend(ts)
        }
        // Term::If(_) => todo!(),
        Term::Lit(l) => l.to_tokens(&mut tokens),
        Term::MethodCall(TermMethodCall {
            receiver,
            dot_token,
            method,
            turbofish,
            args,
            ..
        }) => {
            let r = encode_expr(&receiver)?;
            let args: Vec<_> = args
                .iter()
                .map(|a| encode_expr(a))
                .collect::<syn::Result<_>>()?;

            tokens.extend(quote! { #r #dot_token #method #turbofish ( #(#args),*) })
        }
        Term::Paren(TermParen { expr, .. }) => {
            let inner = encode_expr(expr)?;
            tokens.extend(quote! { ( #inner )})
        }
        Term::Path(p) => tokens.extend(quote!(
            #p
        )),
        Term::Struct(TermStruct { path, fields, .. }) => {
            let fields: Vec<_> = fields
                .iter()
                .map(|f| {
                    let m = &f.member;
                    let t = encode_expr(&f.expr)?;

                    Ok(quote! { #m : #t })
                })
                .collect::<syn::Result<_>>()?;

            tokens.extend(quote! { #path { #(#fields),* } })
        }
        Term::Tuple(TermTuple { elems, .. }) => {
            let fields: Vec<_> = elems
                .iter()
                .map(|a| encode_expr(a))
                .collect::<syn::Result<_>>()?;
            tokens.extend(quote! { ( #(#fields),*) })
        }
        Term::Unary(TermUnary { op, expr }) => {
            let expr = encode_expr(expr)?;

            match op {
                syn::UnOp::Deref(_) => tokens.extend(quote! { (#expr).0 }),
                syn::UnOp::Not(_) => tokens.extend(quote! { ! #expr }),
                syn::UnOp::Neg(_) => tokens.extend(quote! { - #expr }),
                _ => todo!("non-exhaustive unop"),
            }
        }
        Term::Verbatim(v) => v.to_tokens(&mut tokens),
        Term::Cast(TermCast { expr, as_token, ty }) => {
            let expr = encode_expr(expr)?;
            tokens.extend(quote! { #expr #as_token #ty })
        }
        e => {
            return Err(Error::new(
                inner.span(),
                format!("Expression is not supported {e:?}"),
            ))
        }
    };
    Ok(tokens)
}

impl Observation {
    fn encode_inner(inner: &Term) -> syn::Result<TokenStream> {
        encode_expr(inner)
    }

    pub fn encode(&self) -> syn::Result<TokenStream> {
        Self::encode_inner(&self.inner)
    }
}

impl AsrtFragment {
    pub fn encode(&self) -> syn::Result<TokenStream> {
        match self {
            Self::Emp(emp) => {
                let span = emp.span();
                Ok(quote_spanned!(span=> gilogic::__stubs::emp()))
            }
            Self::PointsTo(AsrtPointsTo { left, right, .. }) => {
                Ok(quote!(gilogic::__stubs::PointsTo::points_to(#left, #right)))
            }
            Self::Pure(formula) => {
                let formula = formula.encode()?;
                Ok(quote!(gilogic::__stubs::pure(#formula)))
            }
            Self::Observation(obs) => {
                let observation = obs.encode()?;
                Ok(quote!(gilogic::__stubs::observation(#observation)))
            }
            Self::PredCall(call) => Ok(call.to_token_stream()),
        }
    }
}

// impl ExtractLemma {
//     pub(crate) fn encode(&self, ref_ty: Type, ret_ty: Type) -> syn::Result<TokenStream> {
//         // There's a lot of repetition here, but no time to refactor.

//         let param_ty = if self.prophecise.is_some() {
//             super::utils::repr_type(&super::utils::peel_mut_ref(
//                 ref_ty.clone(),
//                 "Extract lemmas must take a mutable reference as first argument",
//             )?)
//         } else {
//             parse_quote! { () }
//         };

//         let prophecise = match &self.prophecise {
//             Some((_, term)) => {
//                 let models = self.models.as_ref().unwrap();
//                 let model = &models.1;
//                 let new_model = &models.5;
//                 let model_ty = super::utils::repr_type(&super::utils::peel_mut_ref(
//                     ref_ty.clone(),
//                     "Extract lemmas must take a mutable reference as first argument",
//                 )?);
//                 let new_model_ty = super::utils::peel_prophecy_adt(
//                     ret_ty.clone(),
//                     "Extract lemmas must return Prophecy<K> for some K in prophecy mode",
//                 )?;
//                 quote! {
//                     gilogic::__stubs::instantiate_lvars(
//                         #[gillian::no_translate]
//                         |#model: #model_ty, #new_model: #new_model_ty| {
//                             #term
//                         }
//                     )
//                 }
//             }
//             None => quote! { () },
//         };

//         let assuming = match &self.assuming {
//             Some((_, assuming)) => Formula::from_term(assuming.clone()),
//             None => Formula::from_term(parse_quote! {  true == true }),
//         };
//         let assuming = assuming.encode()?;
//         let (_, from) = &self.from;
//         let (_, extract) = &self.extract;
//         let el = quote!(
//             gilogic::__stubs::extract_lemma::<#param_ty>(
//                 #assuming,
//                 #from,
//                 #extract,
//                 #prophecise
//             )
//         );
//         let el = if let Some((_, model, _, _, _, new_model, _)) = &self.models {
//             let model_ty = super::utils::repr_type(&ref_ty);
//             let prophecy_peeled = super::utils::peel_prophecy_adt(
//                 ret_ty.clone(),
//                 "Extract lemmas must return Prophecy<K> for some K in prophecy mode",
//             )?;
//             let new_model_ty: Type = parse_quote! { (#prophecy_peeled, #prophecy_peeled) };

//             quote!( gilogic::__stubs::instantiate_lvars(#[gillian::no_translate] | #model: #model_ty, #new_model: #new_model_ty | { #el }) )
//         } else {
//             el
//         };
//         let foralls = match &self.forall {
//             Some((_, foralls, _)) => foralls,
//             None => &syn::punctuated::Punctuated::new(),
//         };
//         Ok(quote!(
//             unsafe {
//                 gilogic::__stubs::instantiate_lvars(
//                 #[gillian::no_translate]
//                 |#foralls| {
//                     #el
//                 })
//             }
//         ))
//     }
// }

impl SpecEnsures {
    pub fn encode(&self) -> syn::Result<TokenStream> {
        let def = {
            let mut fragments = self.postcond.iter();
            let first = fragments.next().unwrap().encode();
            fragments.fold(first, |acc, fragment| {
                let acc = acc?;
                let right = fragment.encode()?;
                Ok(quote!(gilogic::__stubs::star(#acc, #right)))
            })?
        };

        let rvars = self.rvars.iter();
        let postcond_tokens = quote!({
            gilogic::__stubs::instantiate_lvars(#[gillian::no_translate] |#(#rvars),*| {
                #def
            })
        });

        Ok(postcond_tokens)
    }
}

//
// specification( .. ) fn f. --> fn xxxx_spec( ) { instantiate_lvar( ... )}   #[spec_name = "foo"] fn f( ) { .. }
// specifcation ( .. ) fn lemma --> #[spec_name = "foo" fn lemma( .. ) { instantiate_lvar(...) { let _ = || { specification}; lemma_proof }}

impl Specification {
    pub fn encode(&self) -> syn::Result<TokenStream> {
        // Temporary for easier compatibility with existing code;

        let precond_tokens = {
            let mut fragments = self.precond.iter();
            let first = fragments.next().unwrap().encode();
            fragments.fold(first, |acc, fragment| {
                let acc = acc?;
                let right = fragment.encode()?;
                Ok(quote!(gilogic::__stubs::star(#acc, #right)))
            })?
        };

        let postcond_tokens = self
            .postconds
            .iter()
            .map(|a| a.encode())
            .collect::<syn::Result<Vec<_>>>()?;

        let lvars = self.lvars.iter();

        Ok(quote! {
            unsafe { gilogic::__stubs::instantiate_lvars(#[gillian::no_translate] |#(#lvars),*| {
                gilogic::__stubs::spec(#precond_tokens, [#(#postcond_tokens),*])
            }) }
        })
    }

    pub fn encode_lemma(&self) -> syn::Result<TokenStream> {
        let precond_tokens = {
            let mut fragments = self.precond.iter();
            let first = fragments.next().unwrap().encode();
            fragments.fold(first, |acc, fragment| {
                let acc = acc?;
                let right = fragment.encode()?;
                Ok(quote!(gilogic::__stubs::star(#acc, #right)))
            })?
        };

        let postcond_tokens = self
            .postconds
            .iter()
            .map(|a| a.encode())
            .collect::<syn::Result<Vec<_>>>()?;

        Ok(quote! {
            unsafe {
                gilogic::__stubs::spec(#precond_tokens, [#(#postcond_tokens),*])
            }
        })
    }
}

impl Assertion {
    pub fn encode(&self) -> syn::Result<TokenStream> {
        let mut tokens = TokenStream::new();
        let lvars = self.lvars.iter();
        // Assertion is guaranteed to be a non-empty list of fragments
        let def = {
            let mut fragments = self.def.iter();
            let first = fragments.next().unwrap().encode();
            fragments.fold(first, |acc, fragment| {
                let acc = acc?;
                let right = fragment.encode()?;
                Ok(quote!(gilogic::__stubs::star(#acc, #right)))
            })?
        };
        tokens.extend(quote!({
            unsafe {
                gilogic::__stubs::instantiate_lvars(#[gillian::no_translate] |#(#lvars),*| {
                    #def
                })
            }
        }));
        Ok(tokens)
    }
}

impl ToTokens for PredParamS {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.pat_ty.to_tokens(tokens)
    }
}

impl ToTokens for PredParam {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Self::Receiver(self_token) => self_token.to_tokens(tokens),
            Self::S(s) => s.to_tokens(tokens),
        }
    }
}

fn gather_ins(args: &syn::punctuated::Punctuated<PredParam, syn::token::Comma>) -> String {
    let v: Vec<String> = args
        .iter()
        .enumerate()
        .filter_map(|(i, p)| if p.is_in() { Some(i.to_string()) } else { None })
        .collect();
    v.join(",")
}

impl ToTokens for Predicate {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ins = gather_ins(&self.args);
        let Predicate {
            vis,
            name,
            body,
            generics,
            args,
            attributes,
        } = &self;
        match body {
            None => tokens.extend(quote! {
              #[cfg(gillian)]
              #[gillian::decl::abstract_predicate]
              #[gillian::decl::pred_ins=#ins]
              #(#attributes)*
              #vis fn #name #generics (#args) -> gilogic::RustAssertion {
                unreachable!()
              }
            }),
            Some(body) => {
                let stmts: Vec<_> = body
                    .stmts
                    .clone()
                    .into_iter()
                    .map(|stmt| match stmt {
                        Stmt::Expr(e, Some(_)) => Stmt::Expr(e, None),
                        Stmt::Macro(mut m) => {
                            m.semi_token = None;
                            Stmt::Macro(m)
                        }
                        e => e,
                    })
                    .collect();

                let brace_token = body.brace_token;
                tokens.extend(quote! {
                  #[cfg(gillian)]
                  #[gillian::decl::predicate]
                  #[gillian::decl::pred_ins=#ins]
                  #(#attributes)*
                  #vis fn #name #generics (#args) -> gilogic::RustAssertion
                });
                brace_token.surround(tokens, |tokens| {
                    tokens.extend(quote!(gilogic::__stubs::defs([#(#stmts),*])));
                })
            }
        }
    }
}

impl ToTokens for Lemma {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Lemma {
            pub_token,
            attributes,
            specification,
            sig,
            body,
        } = self;

        let id = Uuid::new_v4().to_string();
        let name = {
            let ident = sig.ident.to_string();
            let name_with_uuid = format!("{}_spec_{}", ident, id).replace('-', "_");
            format_ident!("{}", name_with_uuid, span = Span::call_site())
        };
        let name = name.to_string();
        let spec = specification.encode_lemma().unwrap();
        let ins = format!("{}", sig.inputs.len());
        let uni = specification.lvars.clone();

        let uniargs = uni.iter().map(|lvar| &lvar.ident);
        let spec = quote! {
            let omgomg  =
                (   #[gillian::no_translate]
                    #[gillian::item=#name]
                    #[gillian::decl::specification]
                    #[gillian::decl::pred_ins=#ins]
                |#uni| -> gilogic::RustAssertion { #spec })(#(#uniargs),*);
        };

        let body_toks = match body {
            None => {
                quote! { unreachable!() }
            }
            Some(body) => {
                let stmts = &body.stmts;
                quote! { #(#stmts);* }
            }
        };

        let trusted = if body.is_none() {
            quote! { #[gillian::trusted] }
        } else {
            quote! { }
        };

        tokens.extend(quote! {
            #[cfg(gillian)]
            #(#attributes)*
            #[gillian::decl::lemma]
            #[gillian::spec=#name]
            #trusted
            #pub_token #sig {
                unsafe {
                    gilogic::__stubs::instantiate_lvars(#[gillian::no_translate]
                        |#uni| {
                            #spec;
                            #body_toks
                        }
                    )};
            }
        });
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

        let result = quote! {

            unsafe impl #generics gilogic::prophecies::FrozenOwn<#tuple_arg_ty> for #self_ty {
                    #predicate
            }

            fn #lemma_name #generics (x: &'a mut #self_ty) {
                gilogic::prophecies::freeze_params::<#tuple_arg_ty, #self_ty>(x)
            }

            #[predicate]
            fn #predicate_name #generics (
                this: In<&'a mut #self_ty>,
                model: <&'a mut #self_ty as gilogic::prophecies::Ownable>::RepresentationTy,
                frozen: #tuple_arg_ty
            ) {
                <#self_ty as gilogic::prophecies::FrozenOwn<#tuple_arg_ty>>::mut_ref_own_frozen(this, model, frozen)
            }

            #own_impl
        };

        tokens.extend(result);
    }
}
