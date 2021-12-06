#![no_std]

enum Result {
    Ok(u32),
    Error,
}

use self::Result::*;

fn greater_than_10(x: Result) -> Result {
  match x {
    Ok(u) if u > 10 => x,
    _ => Error
  }
}

fn add_res(x: Result, y: Result) -> Result {
  match (x, y) {
    (Ok(u), Ok(v)) => Ok(u + v),
    _ => Error
  }
} 

pub fn main() {
    let x = Ok(4);
    let y = Ok(7);
    let z = add_res(x, y); // Ok(11)
    let t = Ok(0);
    let k = greater_than_10(z); // Error
    let _res = add_res(k, t); // Error
}
