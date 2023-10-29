use std::collections::HashMap;

use proc_macro2::{Ident, TokenStream};
use syn::{spanned::Spanned, ExprMacro, ExprPath, Item, Path, Token};

use super::*;

pub(crate) trait VarSubst {
    fn subst(&mut self, subst: &HashMap<String, Ident>);
}

impl VarSubst for Ident {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        if let Some(ident) = subst.get(&self.to_string()) {
            *self = ident.clone();
        }
    }
}

impl VarSubst for AsrtEmp {
    fn subst(&mut self, _: &HashMap<String, Ident>) {}
}

impl VarSubst for AsrtPointsTo {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.left.subst(subst);
        self.right.subst(subst);
    }
}

impl VarSubst for AsrtPredCall {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        match self {
            Self::SimpleCall(tc) => tc.subst(subst),
            Self::MethodCall(mc) => mc.subst(subst),
        }
    }
}

impl VarSubst for Formula {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.inner.subst(subst);
    }
}

impl VarSubst for Observation {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.inner.subst(subst);
    }
}

impl VarSubst for TermArray {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.elems.iter_mut().for_each(|e| e.subst(subst));
    }
}

impl VarSubst for TermBinary {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.left.subst(subst);
        self.right.subst(subst);
    }
}

impl VarSubst for TBlock {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.stmts.iter_mut().for_each(|s| s.subst(subst));
    }
}

impl VarSubst for TermStmt {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        match self {
            Self::Local(local) => local.subst(subst),
            Self::Item(item) => item.subst(subst),
            Self::Expr(term) => term.subst(subst),
            Self::Semi(term, _) => term.subst(subst),
        }
    }
}

impl VarSubst for TermBlock {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.block.subst(subst);
    }
}

impl VarSubst for TermCall {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.args.iter_mut().for_each(|a| a.subst(subst));
    }
}

impl VarSubst for TermCast {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.expr.subst(subst);
    }
}

impl VarSubst for TermField {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.base.subst(subst);
    }
}

impl VarSubst for TermGroup {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.expr.subst(subst);
    }
}

impl VarSubst for TermForall {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        let idents_to_not_subst = self.args.iter().map(|x| x.ident.to_string());
        let mut new_subst = subst.clone();
        for ident in idents_to_not_subst {
            new_subst.remove(&ident);
        }
        self.term.subst(&new_subst);
    }
}

impl VarSubst for TermImpl {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.hyp.subst(subst);
        self.cons.subst(subst);
    }
}

impl VarSubst for TermIf {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.cond.subst(subst);
        self.then_branch.subst(subst);
        self.else_branch
            .iter_mut()
            .for_each(|(_, t)| t.subst(subst));
    }
}

impl VarSubst for TermIndex {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.expr.subst(subst);
        self.index.subst(subst);
    }
}

impl VarSubst for TermLit {
    fn subst(&mut self, _subst: &HashMap<String, Ident>) {}
}

impl VarSubst for TermMethodCall {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.receiver.subst(subst);
        self.args.iter_mut().for_each(|a| a.subst(subst));
    }
}

impl VarSubst for TermParen {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.expr.subst(subst);
    }
}

impl VarSubst for TermPath {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.inner.subst(subst)
    }
}

impl VarSubst for ExprPath {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.path.subst(subst);
    }
}

impl VarSubst for Path {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.segments.iter_mut().for_each(|s| s.ident.subst(subst));
    }
}

impl VarSubst for TermReference {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.term.subst(subst);
    }
}

impl VarSubst for TermStruct {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.fields.iter_mut().for_each(|tfv| {
            if tfv.colon_token.is_none() {
                tfv.colon_token = Some(Token![:](tfv.span()))
            }
            tfv.expr.subst(subst)
        });
        self.rest.iter_mut().for_each(|e| e.subst(subst));
    }
}

impl VarSubst for TermTuple {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.elems.iter_mut().for_each(|e| e.subst(subst));
    }
}

impl VarSubst for TermType {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.expr.subst(subst);
    }
}

impl VarSubst for TermUnary {
    fn subst(&mut self, subst: &HashMap<String, Ident>) {
        self.expr.subst(subst);
    }
}

macro_rules! impl_varsubst_todo {
    ($($t:ty),*) => {
        $(
            impl VarSubst for $t {
                fn subst(&mut self, _subst: &HashMap<String, Ident>) {
                    todo!(stringify!($t :: VarSubst))
                }
            }
        )*
    }
}

impl_varsubst_todo!(
    TermClosure,
    TermRange,
    TermRepeat,
    TermMatch,
    TermLet,
    TermArm,
    TokenStream,
    ExprMacro,
    Item,
    TLocal
);
