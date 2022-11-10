extern crate gilogic;

use gilogic::{macros::predicate, Seq};

// #[predicate]
// fn abstract_dll(list: In<LinkedList<T>>, values: Seq<T>);

// #[predicate]
// fn dll(list: In<LinkedList<T>>, values: Seq<T>) {
//     emp * (list == None) * emp * #(list -> LinkedList { head, tail, PhantomData })
// }

struct LinkedList();

// #[predicate]
// fn abstract_linked_list(x: In<LinkedList>, y: Seq<i32>);

#[predicate]
fn new_linked_list(x: In<Option<u32>>) {
    (x == None);
    (x == Some(12))
}

fn main() {}
