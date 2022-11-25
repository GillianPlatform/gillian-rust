use std::collections::HashMap;

use crate::prelude::*;
use gillian::gil::{Assertion, Expr as GExpr, Pred, Type};
use rustc_ast::{Lit, LitKind, MacArgs, MacArgsEq, StrStyle};
use rustc_middle::{
    mir::Field,
    thir::{AdtExpr, ExprId, ExprKind, LocalVarId, Param, Pat, PatKind, StmtKind, Thir},
    ty::{AdtKind, WithOptConstParam},
};

struct PredSig {
    name: String,
    params: Vec<(String, Option<Type>)>,
    ins: Vec<usize>,
    facts: Vec<Formula>,
}

pub(crate) struct PredCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    did: DefId,
    abstract_: bool,
    var_names: HashMap<LocalVarId, String>,
}

impl CanFatal for PredCtx<'_> {
    fn fatal(&self, str: &str) -> ! {
        self.tcx.sess.fatal(str)
    }
}

macro_rules! get_thir {
    ($thir:pat, $expr:pat, $s:expr) => {
        let (___thir, $expr) = $s
            .tcx
            .thir_body(WithOptConstParam::unknown(
                $s.did.as_local().expect("non-local predicate"),
            ))
            .expect("Predicate body failed to typecheck");
        let $thir = ___thir.borrow();
    };
}

// FIXME: this code isn't very elegant, there should be also a "LocalLogCtx" with a reference to the thir body,
//        that would allow to not resolve everything every time. Also, it would be reused for other logic items.
impl<'tcx> PredCtx<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, did: DefId, abstract_: bool) -> Self {
        PredCtx {
            tcx,
            did,
            abstract_,
            var_names: HashMap::new(),
        }
    }

    fn get_ins(&self) -> Vec<usize> {
        let ins_attr = crate::utils::attrs::get_attr(
            self.tcx.get_attrs_unchecked(self.did),
            &["gillian", "decl", "pred_ins"],
        )
        .expect("Predicate must have an ins attribute");

        let str_arg = if let MacArgs::Eq(
            _,
            MacArgsEq::Hir(Lit {
                kind: LitKind::Str(sym, StrStyle::Cooked),
                ..
            }),
        ) = ins_attr.args
        {
            sym.as_str().to_owned()
        } else {
            self.tcx
                .sess
                .fatal("Predicate ins attribute must be a string");
        };

        str_arg
            .split(',')
            .map(|s| s.parse().expect("Ins should be a list of parameter number"))
            .collect()
    }

    fn pred_name(&self) -> String {
        self.tcx.def_path_str(self.did)
    }

    fn extract_param(&mut self, param: &Param<'tcx>) -> (String, Ty<'tcx>) {
        match &param.pat {
            Some(box Pat {
                kind:
                    PatKind::Binding {
                        mutability,
                        name,
                        var,
                        subpattern,
                        is_primary,
                        mode: _,
                        ty: _,
                    },
                ..
            }) => {
                let name = name.to_string();
                let ty = param.ty;
                if !is_primary {
                    fatal!(self, "Predicate parameters must be primary");
                }
                if let Mutability::Mut = mutability {
                    fatal!(self, "Predicate parameters cannot be mutable");
                }
                if subpattern.is_some() {
                    fatal!(self, "Predicate parameters cannot have subpatterns");
                }
                self.var_names.insert(*var, name.clone());
                (name, ty)
            }
            _ => fatal!(self, "Predicate parameters must be variables"),
        }
    }

    fn sig(&mut self) -> PredSig {
        let ins = self.get_ins();
        get_thir!(thir, _expr, self);
        let params = thir
            .params
            .iter()
            .map(|p| self.extract_param(p))
            .map(|(name, _ty)| (name, None))
            .collect::<Vec<_>>();
        PredSig {
            name: self.pred_name(),
            params,
            ins,
            facts: vec![],
        }
    }

    fn compile_abstract(mut self) -> Pred {
        let PredSig {
            name,
            params,
            ins,
            facts,
        } = self.sig();
        Pred {
            name,
            num_params: params.len(),
            params,
            abstract_: true,
            facts,
            definitions: vec![],
            ins,
            pure: false,
        }
    }

    fn is_assertion_ty(&self, ty: Ty<'tcx>) -> bool {
        super::builtins::is_assertion_ty(self.tcx, ty)
    }

    fn is_formula_ty(&self, ty: Ty<'tcx>) -> bool {
        super::builtins::is_formula_ty(self.tcx, ty)
    }

    fn is_call_to(&self, ty: Ty<'tcx>, name: &str) -> bool {
        // TODO: Cache the diagnostic item's type to avoid the cost of lookup every time
        // There is also probably a more direct way of doing this
        if let TyKind::FnDef(did, _) = ty.kind() {
            self.tcx.is_diagnostic_item(Symbol::intern(name), *did)
        } else {
            false
        }
    }

    fn compile_expression(&self, e: ExprId, thir: &Thir<'tcx>) -> GExpr {
        let expr = &thir[e];
        match &expr.kind {
            ExprKind::Scope { value, .. } => self.compile_expression(*value, thir),
            ExprKind::VarRef { id } => match self.var_names.get(id) {
                Some(name) => GExpr::PVar(name.clone()),
                None => {
                    let var_id = id.0.local_id.as_usize();
                    let name = format!("#pred_lvar{}", var_id);
                    GExpr::LVar(name)
                }
            },
            ExprKind::Adt(box AdtExpr {
                adt_def: def,
                variant_index,
                fields,
                base,
                substs: _,
                user_ty: _,
            }) => {
                if base.is_some() {
                    fatal!(self, "Illegal base in logic ADT expression")
                }
                let mut fields_with_idx: Vec<(Field, GExpr)> = fields
                    .iter()
                    .map(|f| (f.name, self.compile_expression(f.expr, thir)))
                    .collect();
                fields_with_idx.sort_by(|(f1, _), (f2, _)| f1.cmp(f2));
                let fields: Vec<GExpr> = fields_with_idx.into_iter().map(|(_, e)| e).collect();
                let adt_name: GExpr = self.tcx.item_name(def.did()).to_string().into();
                match def.adt_kind() {
                    AdtKind::Enum => {
                        let n: GExpr = variant_index.as_u32().into();
                        let value = vec![n, fields.into()].into();
                        vec![adt_name, value].into()
                    }
                    AdtKind::Struct => vec![adt_name, fields.into()].into(),
                    AdtKind::Union => {
                        fatal!(self, "Unions are not supported in logic yet")
                    }
                }
            }
            ExprKind::Literal { lit, neg } => {
                if *neg {
                    fatal!(self, "Negged literal? {:?}", expr)
                }
                match lit.node {
                    LitKind::Int(i, _) => i.into(),
                    _ => fatal!(self, "Unsupported literal {:?}", expr),
                }
            }
            _ => fatal!(self, "{:?} unsupported Thir expression in assertion", expr),
        }
    }

    fn compile_formula(&self, e: ExprId, thir: &Thir<'tcx>) -> Formula {
        let expr = &thir.exprs[e];
        if !self.is_formula_ty(expr.ty) {
            fatal!(self, "{:?} is not the formula type", expr.ty)
        }

        match &expr.kind {
            ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.compile_formula(*value, thir),
            ExprKind::Use { source } => self.compile_formula(*source, thir),
            ExprKind::Call {
                ty, fun: _, args, ..
            } if self.is_call_to(*ty, "gillian::formula::equal") => {
                // FIXME: This doesn't match because equal is polymorphic and it gets monomorphized here.
                assert!(args.len() == 2, "Equal call must have one argument");
                let left = Box::new(self.compile_expression(args[0], thir));
                let right = Box::new(self.compile_expression(args[1], thir));
                Formula::Eq { left, right }
            }
            _ => fatal!(self, "Unsupported formula: {:?}", expr),
        }
    }

    fn compile_assertion(&self, e: ExprId, thir: &Thir<'tcx>) -> Assertion {
        let expr = &thir.exprs[e];
        if !self.is_assertion_ty(expr.ty) {
            fatal!(self, "{:?} is not the assertion type", expr.ty)
        }

        match &expr.kind {
            ExprKind::Scope {
                region_scope: _,
                lint_level: _,
                value,
            } => self.compile_assertion(*value, thir),
            ExprKind::Use { source } => self.compile_assertion(*source, thir),
            ExprKind::Call {
                ty, fun: _, args, ..
            } if self.is_call_to(*ty, "gillian::asrt::pure") => {
                assert!(args.len() == 1, "Pure call must have one argument");
                let formula = self.compile_formula(args[0], thir);
                Assertion::Pure(formula)
            }
            _ => fatal!(self, "Can't compile assertion yet: {:?}", expr),
        }
    }

    fn compile_concrete(mut self) -> Pred {
        let PredSig {
            name,
            params,
            ins,
            facts,
        } = self.sig();
        get_thir!(thir, _expr, self);
        dbg!(&thir, _expr);
        // FIXME: Use the list of statements of the main block expr
        let definitions = thir
            .stmts
            .iter()
            .map(|stmt| match &stmt.kind {
                StmtKind::Let { .. } => fatal!(self, "let statement is not an assertion"),
                StmtKind::Expr { expr, .. } => self.compile_assertion(*expr, &thir),
            })
            .collect();

        Pred {
            name,
            num_params: params.len(),
            params,
            abstract_: false,
            facts,
            definitions,
            ins,
            pure: false,
        }
    }

    pub(crate) fn compile(self) -> Pred {
        if self.abstract_ {
            self.compile_abstract()
        } else {
            self.compile_concrete()
        }
    }
}
