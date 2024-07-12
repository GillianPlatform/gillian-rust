use proc_macro::TokenStream as TokenStream_;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{
    parse_macro_input, FnArg, GenericArgument, ImplItemFn, PatType, PathArguments, Signature, Type,
    TypePath,
};

// Modifies the signature in place, but returns the list of indexes of the `In` arguments.
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
                                GenericArgument::Type(inner_ty) => {
                                    *ty = Box::new(inner_ty.clone());
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
}

// The `#[borrow]` macro applied to a predicate simply adds a guard to the predicate
// which corresponds to a lifetime token. This is done at the compiler level,
// so until then, we really just need to annotate the predicate with some attribute.
pub fn borrow(_args: TokenStream_, input: TokenStream_) -> TokenStream_ {
    let item = parse_macro_input!(input as ImplItemFn);
    // The name of the borrow predicate
    let name = item.sig.ident.clone();

    let sig_without_in_annot = {
        let mut sig = item.sig.clone();
        strip_ins(&mut sig);
        sig
    };

    // The opening lemma signature, it is not the same as the tokens, because it only requires the ins.
    let unfold_ident = format_ident!("{}_____unfold", &name);
    let unfold_ident_diag = "gillian::unfold::".to_string() + &name.to_string();
    let mut unfolder_sig = sig_without_in_annot.clone();
    unfolder_sig.ident = unfold_ident;

    // The closing lemma signature
    let fold_ident = format_ident!("{}_____fold", &name);
    let fold_ident_diag = "gillian::fold::".to_string() + &name.to_string();
    let mut folder_sig = sig_without_in_annot;
    folder_sig.ident = fold_ident;

    let res: TokenStream = quote! {
      #[gillian::borrow]
      #[allow(unused_variables)]
      #[gilogic::macros::predicate]
    //   #lifetimes
      #item

      #[allow(non_snake_case)]
      #[allow(unused_variables)]
      #[gillian::predicate::fold]
      #[rustc_diagnostic_item = #fold_ident_diag]
    //   #lifetimes
      #folder_sig {
        unreachable!()
      }

      #[allow(non_snake_case)]
      #[allow(unused_variables)]
      #[gillian::predicate::unfold]
      #[rustc_diagnostic_item = #unfold_ident_diag]
    //   #lifetimes
      #unfolder_sig {
        unreachable!()
      }
    };
    res.into()
}
