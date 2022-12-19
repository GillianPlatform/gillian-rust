pub(crate) use rustc_middle::ty::TyCtxt;

pub trait CanFatal<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx>;
}

macro_rules! fatal {
  ($e: expr, $($tts:tt)*) => {
      $e.tcx().sess.fatal(&format!($($tts)*))
  };
}

pub(crate) use fatal;
