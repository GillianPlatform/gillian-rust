macro_rules! fatal {
  ($e: expr, $($tts:tt)*) => {
      $e.ty_ctxt.sess.fatal(&format!($($tts)*))
  };
}

pub(crate) use fatal;
