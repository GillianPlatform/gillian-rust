use crate::prelude::*;

pub fn imports() -> Vec<Import> {
    vec![
        Import {
            path: "i__binop.gil".to_string(),
            verify: false,
        },
        Import {
            path: "i__lang.gil".to_string(),
            verify: false,
        },
    ]
}

const CHECKED_ADD: &str = "i__binop_checked_add";
const LANG_ASSERT: &str = "i__lang_assert";

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
