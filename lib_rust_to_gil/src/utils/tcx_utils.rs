use rustc_hir::def_id::DefId;
pub(crate) use rustc_middle::ty::TyCtxt;

pub trait HasTyCtxt<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx>;
}

pub trait HasDefId {
    fn did(&self) -> DefId;
}

macro_rules! fatal {
  ($e: expr, $($tts:tt)*) => {
      $e.tcx().sess.fatal(&format!($($tts)*))
  };
}

pub(crate) use fatal;
