use proc_macro::TokenStream as TokenStream_;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;
use syn::{
    parse_macro_input, punctuated::Punctuated, Block, Expr, ExprMacro, FnArg, GenericArgument,
    ImplItemMethod, Pat, PatIdent, PatType, PathArguments, Signature, Stmt, Token, Type, TypePath,
};

use crate::gilogic_syn::{subst::VarSubst, Assertion, LvarDecl};

// Modifies the signature in place, but returns the list of indexes of the `In` arguments.
fn strip_ins(sig: &mut Signature) -> Vec<usize> {
    let mut ret = vec![];
    for (idx, arg) in sig.inputs.iter_mut().enumerate() {
        if let FnArg::Typed(PatType { ty, .. }) = arg {
            if let Type::Path(TypePath { path, .. }) = &**ty {
                let segment = path.segments.last().unwrap();
                if &segment.ident.to_string() == "In" {
                    match &segment.arguments {
                        PathArguments::None => panic!("`In` used without argument"),
                        PathArguments::Parenthesized(..) => {
                            panic!("`In` used with parenthesize arguments")
                        }
                        PathArguments::AngleBracketed(abga) => {
                            if abga.colon2_token.is_some() || abga.args.len() != 1 {
                                panic!("Invalid arguments for `In`. There should be a single argument without leading double-colon" );
                            }
                            let first = abga.args.first().unwrap();
                            match first {
                                GenericArgument::Type(inner_ty) => {
                                    *ty = Box::new(inner_ty.clone());
                                    ret.push(idx)
                                }
                                _ => {
                                    panic!("Invalid argument for `In`, it should be a single type")
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    ret
}

fn error() -> ! {
    panic!("Expected a single expression in the body of the borrow macro, in the form of `assertion!(|...| ...)`")
}
// This is a horrible hack, right now I'm hiping that the assertion! macro hasn't been expanded yet.
// Moreover, I want to add to the existentials, so I have to isolate them on.
// The following two functions take a block of the form `{ assertion!(|x1, ..., xn| some_assertion) }` and returns the pair of streams
// `x1, ..., xn` and `some_assertion`
fn extract_assertion(block: &Block) -> &TokenStream {
    if block.stmts.len() != 1 {
        error()
    }
    let stmt = block.stmts.first().unwrap();
    match stmt {
        Stmt::Expr(Expr::Macro(ExprMacro { mac, .. })) => {
            if mac.path.segments.last().unwrap().ident != "assertion" {
                error()
            }
            &mac.tokens
        }
        _ => error(),
    }
}

fn extract_arg_name(arg: &FnArg) -> String {
    match arg {
        FnArg::Receiver(_) => "self".to_string(),
        FnArg::Typed(PatType {
            pat: box Pat::Ident(PatIdent { ident, .. }),
            ..
        }) => ident.to_string(),
        _ => panic!("Invalid pattern for lvar"),
    }
}

// The `#[borrow]` macro applied to a predicate generates the following:
// 1) An abstract predicate called `pred_name` which can be opened.
// 2) An abstract predicate called `pred_name$close_token`.
// 3) A lemma `pred_name$access` which exchanges `pred_name` and a token for `'a` for
//      a) the assertion inside `pred_name` and
//      b) a `pred_name$close_token`
// 4) A lemma `pred_name$close` which exchanges the close_token and the assertion against the `pred_name`.
pub fn borrow(_args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    let item = parse_macro_input!(input as ImplItemMethod);

    // The name of the borrow predicate
    let name = item.sig.ident.clone();

    let borrow_token = item.sig.clone();

    // The closing token signature
    let mut close_token = item.sig.clone();
    let close_token_ident = format_ident!("___{}__close_token", &name);
    close_token.ident = close_token_ident.clone();

    let (sig_without_in_annot, ins_indexes) = {
        let mut sig = item.sig.clone();
        let ins_indexes = strip_ins(&mut sig);
        (sig, ins_indexes)
    };

    let sig_with_only_ins = {
        let mut sig = sig_without_in_annot.clone();
        let new_inputs = sig
            .inputs
            .iter()
            .cloned()
            .enumerate()
            .filter_map(|(idx, arg)| {
                if ins_indexes.contains(&idx) {
                    Some(arg)
                } else {
                    None
                }
            })
            .collect();
        sig.inputs = new_inputs;
        sig
    };

    // The opening lemma signature, it is not the same as the tokens, because it only requires the ins.
    let open_lemma_ident = format_ident!("{}_____open", &name);
    let mut open_lemma_sig = sig_with_only_ins.clone();
    open_lemma_sig.ident = open_lemma_ident;

    // The closing lemma signature
    let close_lemma_ident = format_ident!("{}_____close", &name);
    let mut close_lemma_sig = sig_with_only_ins;
    close_lemma_sig.ident = close_lemma_ident;

    // The borrow assertion:
    // 1) We extract from the body of the function and parse it
    // 2) We add create existential for each argument
    // 3) We add the existentials to the assertion's existentials
    // 4) We substitute the program variables for the logical variables created
    // 5) We add the equalities (pvar == lvar) only for variables that are not ins
    // 6) We put everything back together.

    // Step 1
    let borrow_asrt = extract_assertion(&item.block).clone().into();
    let mut borrow_asrt = parse_macro_input!(borrow_asrt as super::gilogic_syn::Assertion);
    // Step 3
    let all_arg_names: Vec<_> = sig_without_in_annot
        .inputs
        .iter()
        .map(extract_arg_name)
        .collect();
    let all_lvar_names: Vec<_> = all_arg_names
        .iter()
        .map(|s| format_ident!("{}___lvar", s))
        .collect();

    // Step 4
    let lvar_decls_to_add = all_lvar_names
        .iter()
        .zip(sig_without_in_annot.inputs.iter())
        .map(|(name, arg)| {
            let name = format_ident!("{}", name);
            match arg {
                FnArg::Receiver(_) => LvarDecl::new(name, None),
                FnArg::Typed(PatType { ty, .. }) => LvarDecl::new(name, Some(*ty.clone())),
            }
        });
    borrow_asrt.lvars.extend(lvar_decls_to_add);

    // Step 5
    let zip = all_arg_names.iter().zip(all_lvar_names.iter());
    let subst: &HashMap<_, _> = &zip.clone().map(|(x, y)| (x.clone(), y.clone())).collect();
    borrow_asrt.def.iter_mut().for_each(|d| d.subst(subst));

    // Step 6
    let equalities: Punctuated<TokenStream, Token![*]> = zip
        .enumerate()
        .filter_map(|(idx, (x, y))| {
            if ins_indexes.contains(&idx) {
                let x = format_ident!("{}", x);
                Some(quote! {(#x == #y)})
            } else {
                None
            }
        })
        .collect();

    let token_pred_call = quote!(#name(#(#all_lvar_names),*));
    let close_token_pred_call = quote!(#close_token_ident(#(#all_lvar_names),*));

    let Assertion {
        pipe1,
        lvars,
        pipe2,
        def,
    } = borrow_asrt;

    let res: TokenStream = quote! {
      #[::gilogic::macros::predicate]
      #borrow_token;

      #[::gilogic::macros::predicate]
      #close_token;

      #[::gilogic::macros::lemma]
      #[::gilogic::macros::requires(#pipe1  #lvars #pipe2 #equalities * #token_pred_call)]
      #[::gilogic::macros::ensures(#pipe1 #lvars #pipe2 #def * #close_token_pred_call)]
      #[gillian::lemma::consumes_lifetime_token]
      #open_lemma_sig;

      #[::gilogic::macros::lemma]
      #[::gilogic::macros::requires(#pipe1 #lvars #pipe2 #equalities * #def * #close_token_pred_call)]
      #[::gilogic::macros::ensures(#pipe1 #lvars #pipe2 #token_pred_call)]
      #[gillian::lemma::produces_lifetime_token]
      #close_lemma_sig;

    };
    res.into()
}
