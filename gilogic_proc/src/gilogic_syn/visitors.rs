use super::asrt::*;

macro_rules! make_visitor {
  ($visitor_trait_name: ident, $($mutability:ident)?) => {
    #[allow(dead_code)]
    pub trait $visitor_trait_name {

      fn visit_term(&mut self, term: &$($mutability)? Term) {
        self.super_term(term);
      }

      fn visit_array(&mut self, array: &$($mutability)? TermArray) {
          self.super_array(array);
      }

      fn visit_binary(&mut self, binary: &$($mutability)? TermBinary) {
          self.super_binary(binary);
      }

      fn visit_block(&mut self, block: &$($mutability)? TermBlock) {
          self.super_block(block);
      }

      fn visit_call(&mut self, call: &$($mutability)? TermCall) {
          self.super_call(call);
      }

      fn visit_cast(&mut self, cast: &$($mutability)? TermCast) {
          self.super_cast(cast);
      }

      fn visit_field(&mut self, field: &$($mutability)? TermField) {
          self.super_field(field);
      }

      fn visit_forall(&mut self, forall: &$($mutability)? TermForall) {
          self.super_forall(forall);
      }

      fn visit_group(&mut self, group: &$($mutability)? TermGroup) {
          self.super_group(group);
      }

      fn visit_if(&mut self, if_: &$($mutability)? TermIf) {
          self.super_if(if_);
      }

      fn visit_impl(&mut self, impl_: &$($mutability)? TermImpl) {
          self.super_impl(impl_);
      }

      fn visit_index(&mut self, index: &$($mutability)? TermIndex) {
          self.super_index(index);
      }

      fn visit_let(&mut self, let_: &$($mutability)? TermLet) {
          self.super_let(let_);
      }

      fn visit_lit(&mut self, lit: &$($mutability)? TermLit) {
          self.super_lit(lit);
      }

      fn visit_match(&mut self, match_: &$($mutability)? TermMatch) {
          self.super_match(match_);
      }

      fn visit_method_call(&mut self, method_call: &$($mutability)? TermMethodCall) {
          self.super_method_call(method_call);
      }

      fn visit_paren(&mut self, paren: &$($mutability)? TermParen) {
          self.super_paren(paren);
      }

      fn visit_path(&mut self, path: &$($mutability)? TermPath) {
          self.super_path(path);
      }

      fn visit_range(&mut self, range: &$($mutability)? TermRange) {
          self.super_range(range);
      }

      fn visit_reference(&mut self, reference: &$($mutability)? TermReference) {
          self.super_reference(reference);
      }

      fn visit_repeat(&mut self, repeat: &$($mutability)? TermRepeat) {
          self.super_repeat(repeat);
      }

      fn visit_struct(&mut self, struct_: &$($mutability)? TermStruct) {
          self.super_struct(struct_);
      }

      fn visit_tuple(&mut self, tuple: &$($mutability)? TermTuple) {
          self.super_tuple(tuple);
      }

      fn visit_type(&mut self, type_: &$($mutability)? TermType) {
          self.super_type(type_);
      }

      fn visit_unary(&mut self, unary: &$($mutability)? TermUnary) {
          self.super_unary(unary);
      }

      fn visit_closure(&mut self, closure: &$($mutability)? TermClosure) {
          self.super_closure(closure);
      }

      fn super_term(&mut self, term: &$($mutability)? Term) {
          match term {
            Term::Array(array) => self.visit_array(array),
            Term::Binary(binary) => self.visit_binary(binary),
            Term::Block(block) => self.visit_block(block),
            Term::Call(call) => self.visit_call(call),
            Term::Cast(cast) => self.visit_cast(cast),
            Term::Field(field) => self.visit_field(field),
            Term::Forall(forall) => self.visit_forall(forall),
            Term::Group(group) => self.visit_group(group),
            Term::If(if_) => self.visit_if(if_),
            Term::Impl(impl_) => self.visit_impl(impl_),
            Term::Index(index) => self.visit_index(index),
            Term::Let(let_) => self.visit_let(let_),
            Term::Lit(lit) => self.visit_lit(lit),
            Term::Match(match_) => self.visit_match(match_),
            Term::MethodCall(method_call) => self.visit_method_call(method_call),
            Term::Paren(paren) => self.visit_paren(paren),
            Term::Path(path) => self.visit_path(path),
            Term::Range(range) => self.visit_range(range),
            Term::Reference(reference) => self.visit_reference(reference),
            Term::Repeat(repeat) => self.visit_repeat(repeat),
            Term::Struct(struct_) => self.visit_struct(struct_),
            Term::Tuple(tuple) => self.visit_tuple(tuple),
            Term::Type(type_) => self.visit_type(type_),
            Term::Unary(unary) => self.visit_unary(unary),
            Term::Closure(closure) => self.visit_closure(closure),
            _ => panic!("Can't visit {:?}", term)
          }
      }

      fn super_array(&mut self, array: &$($mutability)? TermArray) {
          for term in &$($mutability)? array.elems {
             self.visit_term(term)
          };
      }

      fn super_binary(&mut self, binary: &$($mutability)? TermBinary) {
          self.visit_term(&$($mutability)? binary.left);
          self.visit_term(&$($mutability)? binary.right);
      }

      fn super_block(&mut self, block: &$($mutability)? TermBlock) {
          for stmt in &$($mutability)? block.block.stmts {
            match stmt {
              TermStmt::Expr(term) => self.visit_term(term),
              TermStmt::Semi(term, _) => self.visit_term(term),
              _ => panic!("unsupported item or local in gilogic")
            }
          }
      }

      fn super_call(&mut self, call: &$($mutability)? TermCall) {
          self.visit_term(&$($mutability)? call.func);
          for term in &$($mutability)? call.args {
             self.visit_term(term)
          };
      }

      fn super_cast(&mut self, cast: &$($mutability)? TermCast) {
          self.visit_term(&$($mutability)? cast.expr);
      }

      fn super_field(&mut self, field: &$($mutability)? TermField) {
          self.visit_term(&$($mutability)? field.base);
      }

      fn super_forall(&mut self, forall: &$($mutability)? TermForall) {
          self.visit_term(&$($mutability)? forall.term);
      }

      fn super_group(&mut self, group: &$($mutability)? TermGroup) {
          self.visit_term(&$($mutability)? group.expr)
      }

      fn super_if(&mut self, _if_: &$($mutability)? TermIf) {
          panic!("unsupported if expression in gilogic")
      }

      fn super_impl(&mut self, impl_: &$($mutability)? TermImpl) {
          self.visit_term(&$($mutability)? impl_.hyp);
          self.visit_term(&$($mutability)? impl_.cons);
      }

      fn super_index(&mut self, index: &$($mutability)? TermIndex) {
          self.visit_term(&$($mutability)? index.expr);
          self.visit_term(&$($mutability)? index.index);
      }

      fn super_let(&mut self, _let_: &$($mutability)? TermLet) {
          panic!("Unsupported let expr in gilogic");
      }

      fn super_lit(&mut self, _lit: &$($mutability)? TermLit) {

      }

      fn super_match(&mut self, _match_: &$($mutability)? TermMatch) {
        panic!("Unsupported match expr in gilogic");
      }

      fn super_method_call(&mut self, method_call: &$($mutability)? TermMethodCall) {
          self.visit_term(&$($mutability)? method_call.receiver);
          for args in &$($mutability)? method_call.args {
            self.visit_term(args)
          }
      }

      fn super_paren(&mut self, paren: &$($mutability)? TermParen) {
          self.visit_term(&$($mutability)? paren.expr);
      }

      fn super_path(&mut self, _path: &$($mutability)? TermPath) {}

      fn super_range(&mut self, range: &$($mutability)? TermRange) {
          if let Some(from) = &$($mutability)? range.from {
            self.visit_term(from)
          }
          if let Some(to) = &$($mutability)? range.to {
            self.visit_term(to)
          }

      }

      fn super_reference(&mut self, reference: &$($mutability)? TermReference) {
          self.visit_term(&$($mutability)? reference.term);
      }

      fn super_repeat(&mut self, repeat: &$($mutability)? TermRepeat) {
          self.visit_term(&$($mutability)? repeat.expr);
          self.visit_term(&$($mutability)? repeat.len);
      }

      fn super_struct(&mut self, struct_: &$($mutability)? TermStruct) {
        if let Some(rest) = &$($mutability)? struct_.rest {
          self.visit_term(rest);
        }
        for field in &$($mutability)? struct_.fields {
          self.visit_term(&$($mutability)? field.expr)
        }
      }

      fn super_tuple(&mut self, tuple: &$($mutability)? TermTuple) {
          for elem in &$($mutability)? tuple.elems {
            self.visit_term(elem)
          }
      }

      fn super_type(&mut self, type_: &$($mutability)? TermType) {
          self.super_term(&$($mutability)? type_.expr);
      }

      fn super_unary(&mut self, unary: &$($mutability)? TermUnary) {
          self.super_term(&$($mutability)? unary.expr);
      }

      fn super_closure(&mut self, closure: &$($mutability)? TermClosure) {
          self.visit_term(&$($mutability)? closure.body);
      }


    }
  }
}

make_visitor!(Visitor,);
make_visitor!(VisitorMut, mut);
