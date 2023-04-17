use proc_macro::TokenStream as TS1;
use quote::{format_ident, ToTokens};
use syn::{parse_macro_input, Expr, ExprCall, ExprMethodCall, ExprPath, Path};

pub fn add_to_call_name(input: TS1, suffix: &str) -> TS1 {
    let mut expr = parse_macro_input!(input as Expr);
    match &mut expr {
        Expr::Call(ExprCall {
            func:
                box Expr::Path(ExprPath {
                    path: Path { segments, .. },
                    ..
                }),
            ..
        }) => {
            let last = segments.last_mut().unwrap();
            last.ident = format_ident!("{}{}", last.ident, suffix);
        }
        Expr::MethodCall(ExprMethodCall { method, .. }) => {
            *method = format_ident!("{}{}", method, suffix);
        }
        _ => {
            return syn::Error::new_spanned(expr, "Expected a call or method call")
                .to_compile_error()
                .into();
        }
    };
    expr.to_token_stream().into()
}
