//@check-pass
extern crate gilogic;
use gilogic::macros::*;
use gilogic::Ownable;

// #[show_safety]
fn swap_borrows<'a, 'b>(x : &'a mut i32, y: &'b mut i32) -> (&'b mut i32, &'a mut i32) {
  (y, x)
}

#[show_safety]
fn fst<'a, 'b>(x : &'a mut i32, y: &'b mut i32) -> (&'a mut i32) {
  x
}


#[show_safety]
fn snd<'a, 'b>(x : &'a mut i32, y: &'b mut i32) -> (&'b mut i32) {
  y
}

// #[show_safety]
// fn swap<T: Ownable, U : Ownable>(x : T, y : U) -> (U, T) {
//   (y, x)
// }

// #[show_safety]
// fn swap_borrows2<'a, 'b>(x : &'a mut i32, y: &'b mut i32) -> (&'b mut i32, &'a mut i32) {
//   swap(x, y)
// }

// fn test() {
//   let mut x = 0;
//   let mut y = 1;

//   let (a, b) = swap_borrows2(&mut x, &mut y);
//   let (c, d) = swap_borrows(a, b);

//   *c = 5;
//   *d = 10;

//   assert!(x == 5);
//   assert!(y == 10);
// }