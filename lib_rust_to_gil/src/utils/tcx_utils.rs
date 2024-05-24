use rustc_hir::def_id::DefId;
pub(crate) use rustc_middle::ty::TyCtxt;

pub trait HasTyCtxt<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx>;
}

pub trait HasDefId {
    fn did(&self) -> DefId;
}

impl<'tcx> HasDefId for (DefId, TyCtxt<'tcx>) {
    fn did(&self) -> DefId {
        self.0
    }
}

impl<'tcx> HasTyCtxt<'tcx> for (DefId, TyCtxt<'tcx>) {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.1
    }
}

macro_rules! fatal {
  ($e: expr, $($tts:tt)*) => {
      $e.tcx().dcx().fatal(format!($($tts)*))
  };
}

macro_rules! fatal2 {
  ($e: expr, $($tts:tt)*) => {
      $e.dcx().fatal(format!($($tts)*))
  };
}

pub(crate) use fatal;
pub(crate) use fatal2;
