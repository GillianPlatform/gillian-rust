use std::collections::HashMap;

use super::*;

macro_rules! make_gil_visitor {
    ($visitor_trait_name:ident, $($mutability:ident)?) => {
      pub trait $visitor_trait_name {

        fn visit_cmd(&mut self, cmd: &$($mutability)? Cmd) {
          self.super_cmd(cmd);
        }

        fn visit_lcmd(&mut self, lcmd: &$($mutability)? LCmd) {
          self.super_lcmd(lcmd);
        }

        fn visit_slcmd(&mut self, slcmd: &$($mutability)? SLCmd) {
          self.super_slcmd(slcmd);
        }

        fn visit_assertion(&mut self, assertion: &$($mutability)? Assertion) {
          self.super_assertion(assertion);
        }

        fn visit_formula(&mut self, formula: &$($mutability)? Formula) {
          self.super_formula(formula);
        }

        fn visit_expr(&mut self, expr: &$($mutability)? Expr) {
          self.super_expr(expr);
        }

        fn visit_binop(&mut self, binop: &$($mutability)? BinOp) {
          self.super_binop(binop);
        }

        fn visit_unop(&mut self, unop: &$($mutability)? UnOp) {
          self.super_unop(unop);
        }

        fn visit_nop(&mut self, nop: &$($mutability)? NOp) {
          self.super_nop(nop);
        }

        fn visit_type(&mut self, ty: &$($mutability)? Type) {
          self.super_type(ty);
        }

        fn visit_literal(&mut self, literal: &$($mutability)? Literal) {
          self.super_literal(literal);
        }

        fn visit_constant(&mut self, constant: &$($mutability)? Constant) {
          self.super_constant(constant);
        }

        fn super_assertion(&mut self, assertion: &$($mutability)? Assertion) {
          match assertion {
            Assertion::Emp => (),
            Assertion::Star { left, right } => {
              self.visit_assertion(left);
              self.visit_assertion(right);
            },
            Assertion::Pred { name:_, params } => {
              for param in params {
                self.visit_expr(param);
              }
            },
            Assertion::Pure(formula) => {
              self.visit_formula(formula);
            },
            Assertion::Types(tys) => {
              for (expr, ty) in tys {
                self.visit_expr(expr);
                self.visit_type(ty);
              }
            },
            Assertion::GA { name:_, ins, outs } => {
              for in_ in ins {
                self.visit_expr(in_);
              }
              for out in outs {
                self.visit_expr(out);
              }
            },
            Assertion::Wand { lhs, rhs } => {
              for expr in &$($mutability)? lhs.1 {
                self.visit_expr(expr);
              }
              for expr in &$($mutability)? rhs.1 {
                self.visit_expr(expr);
              }
            }
          }
        }

        fn super_formula(&mut self, formula: &$($mutability)? Formula) {
          match formula {
            Formula::True | Formula::False => (),
            Formula::Not(f) => {
              self.visit_formula(f);
            },
            Formula::And { left, right }
            | Formula::Or { left, right }
            | Formula::Impl { left, right } => {
              self.visit_formula(left);
              self.visit_formula(right);
            },
            Formula::Eq { left, right }
            | Formula::ILess { left, right }
            | Formula::ILessEq { left, right }
            | Formula::FLess { left, right }
            | Formula::FLessEq { left, right }
            | Formula::StrLess { left, right }
            | Formula::SetMem { left, right }
            | Formula::SetSub { left, right } => {
              self.visit_expr(left);
              self.visit_expr(right);
            },
            Formula::ForAll { quantified, formula } => {
              for (_, ty) in quantified {
                if let Some(ty) = ty {
                  self.visit_type(ty);
                }
              }
              self.visit_formula(formula);
            }
          }
        }

        fn super_cmd(&mut self, cmd: &$($mutability)? Cmd) {
          match cmd {
            Cmd::Skip | Cmd::Goto(_) | Cmd::ReturnNormal | Cmd::ReturnError => (),
            Cmd::Assignment { variable: _, assigned_expr } => {
              self.visit_expr(assigned_expr);
            },
            Cmd::Action{ variable: _, action_name: _, parameters } => {
              for param in parameters {
                self.visit_expr(param);
              }
            },
            Cmd::Call { variable: _, proc_ident: _, parameters, error_lab: _, bindings } => {
              for param in parameters {
                self.visit_expr(param);
              }
              if let Some(bindings) = bindings {
                for (_, expr) in &$($mutability)? bindings.binds {
                  self.visit_expr(expr);
                }
              }
            },
            Cmd::ECall { variable: _, proc_ident, parameters, error_lab: _ } => {
              self.visit_expr(proc_ident);
              for param in parameters {
                self.visit_expr(param);
              }
            },
            Cmd::Apply { variable: _, args, error_lab: _ } => {
              self.visit_expr(args);
            }
            Cmd::PhiAssignment(phis) => {
              for phi in phis {
                for expr in &$($mutability)? phi.values {
                  self.visit_expr(expr);
                }
              }
            },
            Cmd::Logic(lcmd) => {
              self.visit_lcmd(lcmd);
            },
            Cmd::Fail { name: _, parameters } => {
              for param in parameters {
                self.visit_expr(param);
              }
            },
            Cmd::GuardedGoto { guard, then_branch: _, else_branch: _ } => {
              self.visit_expr(guard);
            },
          }
        }

        fn super_lcmd(&mut self, lcmd: &$($mutability)? LCmd) {
          match lcmd {
            LCmd::If { guard, then_branch, else_branch } => {
              self.visit_expr(guard);
              self.visit_lcmd(then_branch);
              self.visit_lcmd(else_branch);
            },
            LCmd::Branch(formula) | LCmd::Assert(formula) | LCmd::Assume(formula) => {
              self.visit_formula(formula);
            },
            LCmd::AssumeType { variable: _, typ } => {
              self.visit_type(typ);
            },
            LCmd::FreshSVar(_) => (),
            LCmd::SL(slcmd) => {
              self.visit_slcmd(slcmd);
            },
          }
        }

        fn super_slcmd(&mut self, slcmd: &$($mutability)? SLCmd) {
          match slcmd {
            SLCmd::Fold { pred_name: _, parameters, bindings }
            | SLCmd::Unfold { pred_name: _, parameters, bindings, rec: _ } => {
              for param in parameters {
                self.visit_expr(param);
              }
              if let Some(bindings) = bindings {
                for (_, expr) in &$($mutability)? bindings.binds {
                  self.visit_expr(expr);
                }
              }
            },
            SLCmd::Package { lhs, rhs } => {
              for expr in &$($mutability)? lhs.1 {
                self.visit_expr(expr);
              }
              for expr in &$($mutability)? rhs.1 {
                self.visit_expr(expr);
              }
            },
            SLCmd::ApplyLem { lemma_name: _, parameters, existentials: _} => {
              for param in parameters {
                self.visit_expr(param);
              }
            }
            SLCmd::SepAssert { assertion, existentials: _ } | SLCmd::Invariant { assertion, existentials: _ } => {
              self.visit_assertion(assertion);
            },
            SLCmd::GUnfold(_) => (),
          }
        }

        fn super_expr(&mut self, expr: &$($mutability)? Expr) {
          match expr {
            Expr::Lit(literal) => self.visit_literal(literal),
            Expr::PVar(_) | Expr::LVar(_) | Expr::ALoc(_) => (),
            Expr::UnOp { operator, operand } => {
              self.visit_unop(operator);
              self.visit_expr(operand);
            }
            Expr::BinOp { operator, left_operand, right_operand } => {
              self.visit_binop(operator);
              self.visit_expr(left_operand);
              self.visit_expr(right_operand);
            }
            Expr::NOp { operator, operands } => {
              self.visit_nop(operator);
              for operand in operands {
                self.visit_expr(operand);
              }
            }
            Expr::LstSub { list, start, length } => {
              self.visit_expr(list);
              self.visit_expr(start);
              self.visit_expr(length);
            }
            Expr::EList(exprs) | Expr::ESet(exprs) => {
              for expr in exprs {
                self.visit_expr(expr);
              }
            }
          }
        }

        fn super_literal(&mut self, literal: &$($mutability)? Literal) {
          match literal {
            Literal::Num(_)
            | Literal::Int(_)
            | Literal::Bool(_)
            | Literal::String(_)
            | Literal::Loc(_)
            | Literal::Null
            | Literal::Nono
            | Literal::Empty
            | Literal::Undefined => (),
            | Literal::Constant(constant) => self.visit_constant(constant),
            | Literal::Type(ty) => self.visit_type(ty),
            | Literal::LList(literals) => {
              for literal in literals {
                self.visit_literal(literal);
              }
            }
          }
        }

        fn super_type(&mut self, _ty: &$($mutability)? Type) {}

        fn super_binop(&mut self, _binop: &$($mutability)? BinOp) {}

        fn super_unop(&mut self, _unop: &$($mutability)? UnOp) {}

        fn super_nop(&mut self, _unop: &$($mutability)? NOp) {}

        fn super_constant(&mut self, _constant: &$($mutability)? Constant) {}
      }
    };
}

pub struct SubstPVar<'a>(&'a HashMap<String, Expr>);

impl<'a> SubstPVar<'a> {
    pub fn new(mapping: &'a HashMap<String, Expr>) -> Self {
        Self(mapping)
    }
}

impl<'a> GilVisitorMut for SubstPVar<'a> {
    fn visit_lcmd(&mut self, _lcmd: &mut LCmd) {
        panic!("SubstPVar::visit_lcmd! shouldn't be called where pvars are used as identifiers and not exprs")
    }

    fn visit_slcmd(&mut self, _slcmd: &mut SLCmd) {
        panic!("SubstPVar::visit_slcmd! shouldn't be called where pvars are used as identifiers and not exprs")
    }

    fn visit_cmd(&mut self, _cmd: &mut Cmd) {
        panic!("SubstPVar::visit_cmd! shouldn't be called where pvars are used as identifiers and not exprs")
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        match expr {
            Expr::PVar(s) => {
                if let Some(e) = self.0.get(s) {
                    *expr = e.clone();
                }
            }
            _ => self.super_expr(expr),
        }
    }
}

make_gil_visitor!(GilVisitor,);
make_gil_visitor!(GilVisitorMut, mut);
