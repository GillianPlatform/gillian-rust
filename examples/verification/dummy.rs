extern crate gilogic;

use gilogic::{macros::predicate, Seq};

// #[predicate]
// fn abstract_dll(list: In<LinkedList<T>>, values: Seq<T>);

// #[predicate]
// fn dll(list: In<LinkedList<T>>, values: Seq<T>) {
//     emp * (list == None) * emp * #(list -> LinkedList { head, tail, PhantomData })
// }

struct LinkedList();

#[predicate]
fn new_linked_list(x: In<LinkedList>, alpha: Seq<u32>);

fn main() {}
