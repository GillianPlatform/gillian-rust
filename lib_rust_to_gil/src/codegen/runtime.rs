use crate::prelude::*;

macro_rules! import {
    ($e: expr) => {
        Import {
            path: $e.to_string(),
            verify: false,
        }
    };
}

pub fn imports(prophecy_mode: bool) -> Vec<Import> {
    let mut ret = vec![
        import!("i__binop.gil"),
        import!("i__lang.gil"),
        import!("i__std_shims.gil"),
        import!("i__prophecies.gil"),
    ];
    if prophecy_mode {
        ret.push(import!("i__ownable_pcy.gil"));
        ret.push(import!("i__std_shims_pcy.gil"));
    } else {
        ret.push(import!("i__ownable.gil"));
        ret.push(import!("i__std_shims_no_pcy.gil"));
    }
    ret
}

const CHECKED_ADD: &str = "i__binop_checked_add";
const CHECKED_SUB: &str = "i__binop_checked_sub";
const CHECKED_MUL: &str = "i__binop_checked_mul";
const LANG_ASSERT: &str = "i__lang_assert";
const _INT_OF_BOOL: &str = "i__lang_int_of_bool";
const _BOOL_OF_INT: &str = "i__bool_of_lang_int";

pub fn checked_add(variable: String, e1: Expr, e2: Expr, max_val: Expr) -> Cmd {
    Cmd::Call {
        variable,
        proc_ident: Expr::string(CHECKED_ADD.to_string()),
        parameters: vec![e1, e2, max_val],
        error_lab: None,
        bindings: None,
    }
}

pub fn checked_sub(variable: String, e1: Expr, e2: Expr) -> Cmd {
    Cmd::Call {
        variable,
        proc_ident: Expr::string(CHECKED_SUB.to_string()),
        parameters: vec![e1, e2],
        error_lab: None,
        bindings: None,
    }
}

pub fn checked_mul(variable: String, e1: Expr, e2: Expr) -> Cmd {
    Cmd::Call {
        variable,
        proc_ident: Expr::string(CHECKED_MUL.to_string()),
        parameters: vec![e1, e2],
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

// We might use this later for casts involving booleans.
fn _bool_of_int(variable: String, int_expr: Expr) -> Cmd {
    Cmd::Call {
        variable,
        proc_ident: _BOOL_OF_INT.into(),
        parameters: vec![int_expr],
        error_lab: None,
        bindings: None,
    }
}

fn _int_of_bool(variable: String, bool_expr: Expr) -> Cmd {
    Cmd::Call {
        variable,
        proc_ident: Expr::string(_INT_OF_BOOL.to_string()),
        parameters: vec![bool_expr],
        error_lab: None,
        bindings: None,
    }
}
