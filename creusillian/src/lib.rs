extern crate proc_macro;
use pearlite_syn::{Term, TermBinary, TermCall, TermMethodCall, TermParen};
use proc_macro::TokenStream as TokenStream_;
use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse_macro_input,
    punctuated::{Pair, Punctuated},
    spanned::Spanned,
    token::{Comma, Paren},
    BinOp, Error, Ident,
};

struct Ctx {
    created_vars: u32,
    models: Vec<(Ident, TokenStream)>,
}

fn is_gil_formula_op(op: BinOp) -> bool {
    use BinOp::*;
    matches!(op, Eq(_) | Lt(_) | Gt(_) | Le(_) | Ge(_))
}

impl Ctx {
    fn new() -> Self {
        Self {
            created_vars: 0,
            models: vec![],
        }
    }

    fn ident(i: u32) -> Ident {
        format_ident!("lvar_{}", i)
    }

    fn fresh_var(&mut self) -> Ident {
        let var = Self::ident(self.created_vars);
        self.created_vars += 1;
        var
    }

    fn translate_args(
        &mut self,
        paren_token: Paren,
        args: Punctuated<Term, Comma>,
    ) -> syn::Result<TokenStream> {
        let mut err = None;
        let mut stream = TokenStream::new();
        paren_token.surround(&mut stream, |stream| {
            for pair in args.into_pairs() {
                match pair {
                    Pair::Punctuated(term, comma) => {
                        let term = match self.translate_expression(term) {
                            Err(e) => {
                                err = Some(e);
                                return;
                            }
                            Ok(x) => x,
                        };
                        term.to_tokens(stream);
                        comma.to_tokens(stream);
                    }
                    Pair::End(term) => {
                        let term = match self.translate_expression(term) {
                            Err(e) => {
                                err = Some(e);
                                return;
                            }
                            Ok(x) => x,
                        };
                        term.to_tokens(stream);
                    }
                }
            }
        });
        if let Some(err) = err {
            Err(err)
        } else {
            Ok(stream)
        }
    }

    fn translate_expression(&mut self, term: Term) -> syn::Result<TokenStream> {
        match term {
            Term::Model(model_term) => {
                let ident = self.fresh_var();
                let term = self.translate_expression(*model_term.term)?;
                self.models.push((ident.clone(), term));
                Ok(ident.to_token_stream())
            }
            Term::Paren(TermParen { paren_token, expr }) => {
                let mut stream = TokenStream::new();
                let mut err = None;
                paren_token.surround(&mut stream, |stream| {
                    match self.translate_expression(*expr) {
                        Err(e) => err = Some(e),
                        Ok(x) => x.to_tokens(stream),
                    }
                });
                if let Some(err) = err {
                    Err(err)
                } else {
                    Ok(stream)
                }
            }
            Term::Call(TermCall {
                func,
                paren_token,
                args,
            }) => {
                let mut stream = func.to_token_stream();
                stream.extend(self.translate_args(paren_token, args)?);
                Ok(stream)
            }
            Term::MethodCall(TermMethodCall {
                receiver,
                dot_token,
                method,
                turbofish,
                paren_token,
                args,
            }) => {
                let receiver = self.translate_expression(*receiver)?;
                let args = self.translate_args(paren_token, args)?;
                Ok(quote!(
                    #receiver #dot_token #method #turbofish #args
                ))
            }
            Term::Path(_) | Term::Lit(_) => Ok(term.to_token_stream()),
            _ => Err(Error::new(
                term.span(),
                format!("Unsupported expression {:?}", term),
            )),
        }
    }

    fn translate_assertion(&mut self, term: Term) -> syn::Result<TokenStream> {
        match term {
            Term::Binary(TermBinary {
                op: BinOp::And(tok),
                left,
                right,
            }) => {
                let left = self.translate_assertion(*left)?;
                let right = self.translate_assertion(*right)?;
                let star = syn::token::Star(tok.span());
                let result = quote!(
                    #left #star #right
                );
                Ok(result)
            }
            Term::Binary(TermBinary { op, left, right }) if is_gil_formula_op(op) => {
                let left = self.translate_expression(*left)?;
                let right = self.translate_expression(*right)?;
                let tok = op.to_token_stream();
                let result = quote!(
                    (#left #tok #right)
                );
                Ok(result)
            }
            _ => Err(Error::new(term.span(), "Unsupported assertion")),
        }
    }

    fn models(&self) -> syn::Result<TokenStream> {
        let mut result = TokenStream::new();
        let mut first = true;
        for (ident, term) in &self.models {
            if first {
                first = false
            } else {
                result.extend(quote!(*));
            }
            result.extend(quote!(::gilogic::ShallowRepresentation::shallow_repr(#term, #ident)));
        }
        Ok(result)
    }

    fn translate_root_term(term: Term) -> syn::Result<TokenStream> {
        let mut ctx = Ctx::new();
        let gil = ctx.translate_assertion(term)?;
        let lvars = (0..ctx.created_vars).map(Self::ident);
        let models = ctx.models()?;
        let result = quote!(|#(#lvars),*| #gil * #models);
        Ok(result)
    }
}

#[proc_macro_attribute]
pub fn requires(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    let input: TokenStream = input.into();
    let term = parse_macro_input!(args as Term);
    let gilogic = match Ctx::translate_root_term(term) {
        Ok(x) => x,
        Err(e) => return e.to_compile_error().into(),
    };
    dbg!(gilogic.to_string());
    quote!(
      #[::gilogic::macros::requires(#gilogic)]
      #input
    )
    .into()
}

#[proc_macro_attribute]
pub fn ensures(args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    let input: TokenStream = input.into();
    let term = parse_macro_input!(args as Term);
    let gilogic = match Ctx::translate_root_term(term) {
        Ok(x) => x,
        Err(e) => return e.to_compile_error().into(),
    };
    quote!(
      #[::gilogic::macros::ensures(#gilogic)]
      #input
    )
    .into()
}
