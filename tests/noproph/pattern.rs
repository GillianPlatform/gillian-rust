//@check-pass
extern crate gilogic;

use gilogic::{macros::*, Ownable};

#[specification(
  requires { emp }
  ensures { emp }
)]
fn test((a, b): (i32, i32)) -> i32 {
    return 0;
}
