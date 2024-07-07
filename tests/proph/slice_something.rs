//@check-pass
extern crate gilogic;
use gilogic::{macros::specification, prophecies::Ownable};
use std::slice::from_raw_parts_mut;

fn test(x: &mut [u32]) -> u32 {
    x[0]
}

#[specification(
  forall m.
  requires { (x -> m) * m.own(m) }
  ensures { ret.own(m) }
)]
pub fn test2(x: *mut u32) -> u32 {
    let x = unsafe { from_raw_parts_mut(x, 1) };
    test(x)
}
