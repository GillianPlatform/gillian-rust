pub trait CanFatal {
    fn fatal(&self, str: &str) -> !;
}

macro_rules! fatal {
  ($e: expr, $($tts:tt)*) => {
      $e.fatal(&format!($($tts)*))
  };
}

pub(crate) use fatal;
