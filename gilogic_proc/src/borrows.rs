use proc_macro::TokenStream as TokenStream_;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;
use syn::{
    parse_macro_input, punctuated::Punctuated, Block, Expr, ExprMacro, FnArg, GenericArgument,
    ImplItemMethod, Pat, PatIdent, PatType, PathArguments, Signature, Stmt, Token, Type, TypePath,
};
use uuid::Uuid;

use crate::gilogic_syn::{subst::VarSubst, Assertion, LvarDecl};

fn strip_ins(sig: &mut Signature) {
    for arg in sig.inputs.iter_mut() {
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
                                GenericArgument::Type(inner_ty) => *ty = Box::new(inner_ty.clone()),
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

    let borrow_id = Uuid::new_v4().to_string();
    let close_token_diag = format!("close_token_{borrow_id}");
    let borrow_token = item.sig.clone();

    // The closing token signature
    let mut close_token = item.sig.clone();
    let close_token_ident = format_ident!("___{}__close_token", &name);
    close_token.ident = close_token_ident.clone();

    // The opening lemma signature
    let open_lemma_ident = format_ident!("{}_____open", &name);
    let mut open_lemma_sig = item.sig.clone();
    strip_ins(&mut open_lemma_sig);
    open_lemma_sig.ident = open_lemma_ident;

    // The closing lemma signature
    let close_lemma_ident = format_ident!("{}_____close", &name);
    let mut close_lemma_sig = open_lemma_sig.clone();
    close_lemma_sig.ident = close_lemma_ident;

    // The borrow assertion:
    // 1) We extract from the body of the function
    // 2) We parse it
    // 3) We add create existential for each argument
    // 4) We add the existentials to the assertion's existentials
    // 5) We substitute the program variables for the logical variables created
    // 6) We add the equalities (pvar == lvar)
    // 7) We put everything back together.

    // Step 1
    let borrow_asrt = extract_assertion(&item.block).clone().into();
    // Step 2
    let mut borrow_asrt = parse_macro_input!(borrow_asrt as super::gilogic_syn::Assertion);
    // Step 3
    let args: Vec<_> = item.sig.inputs.iter().map(extract_arg_name).collect();
    let param_lvars: Vec<_> = args.iter().map(|s| format_ident!("{}___lvar", s)).collect();

    // Step 4
    let lvar_decls_to_add =
        param_lvars
            .iter()
            .zip(open_lemma_sig.inputs.iter())
            .map(|(name, arg)| {
                let name = format_ident!("{}", name);
                match arg {
                    FnArg::Receiver(_) => LvarDecl::new(name, None),
                    FnArg::Typed(PatType { ty, .. }) => LvarDecl::new(name, Some(*ty.clone())),
                }
            });
    borrow_asrt.lvars.extend(lvar_decls_to_add);

    // Step 5
    let zip = args.iter().zip(param_lvars.iter());
    let subst: &HashMap<_, _> = &zip.clone().map(|(x, y)| (x.clone(), y.clone())).collect();

    borrow_asrt.def.iter_mut().for_each(|d| d.subst(subst));

    // Step 6
    let equalities: Punctuated<TokenStream, Token![*]> = zip
        .map(|(x, y)| {
            let x = format_ident!("{}", x);
            quote! {(#x == #y)}
        })
        .collect();

    let token_pred_call = quote!(#name(#(#param_lvars),*));
    let close_token_pred_call = quote!(#close_token_ident(#(#param_lvars),*));

    let Assertion {
        pipe1,
        lvars,
        pipe2,
        def,
    } = borrow_asrt;

    let res: TokenStream = quote! {
      #[gillian::close_token = #close_token_diag]
      #[::gilogic::macros::predicate]
      #borrow_token;

      #[rustc_diagnostic_item = #close_token_diag]
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
