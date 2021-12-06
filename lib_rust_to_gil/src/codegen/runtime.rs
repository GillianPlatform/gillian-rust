use crate::prelude::*;

macro_rules! import {
    ($e: expr) => {
        Import {
            path: $e.to_string(),
            verify: false,
        }
    };
}

pub fn imports() -> Vec<Import> {
    vec![import!("i__binop.gil"), import!("i__lang.gil")]
}

const CHECKED_ADD: &str = "i__binop_checked_add";
const LANG_ASSERT: &str = "i__lang_assert";
const INT_OF_BOOL: &str = "i__lang_int_of_bool";

pub fn checked_add(variable: String, e1: Expr, e2: Expr, max_val: Expr) -> Cmd {
    Cmd::Call {
        variable,
        proc_ident: Expr::string(CHECKED_ADD.to_string()),
        parameters: vec![e1, e2, max_val],
        error_lab: None,
        bindings: None,
    }
}

pub fn lang_assert(cond: Expr, msg: String) -> Cmd {
    Cmd::Call {
        variable: names::unused_var(),
        proc_ident: Expr::string(LANG_ASSERT.to_string()),
        parameters: vec![cond, Expr::string(msg)],
        error_lab: None,
        bindings: None,
    }
}

pub fn int_of_bool(variable: String, bool_expr: Expr) -> Cmd {
    Cmd::Call {
        variable,
        proc_ident: Expr::string(INT_OF_BOOL.to_string()),
        parameters: vec![bool_expr],
        error_lab: None,
        bindings: None,
    }
}
