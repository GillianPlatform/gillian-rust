use super::LogicItem;
use crate::signature::{build_signature, ParamKind};
use crate::{prelude::*, signature};
use gillian::gil::{Assertion, Expr, LCmd, Lemma, SLCmd};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::GenericArgs;

use crate::temp_gen::TempGenerator;
use crate::{
    codegen::typ_encoding::TypeEncoder,
    prelude::{fatal, HasDefId, HasTyCtxt},
};

struct LemmaSig {
  name: String,
  params: Vec<String>,
}

pub(crate) struct ExtractLemmaCtx<'tcx, 'genv> {
  global
}