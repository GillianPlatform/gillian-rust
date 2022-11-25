extern crate gilogic;

use gilogic::{
    macros::{assertion, predicate},
    Seq,
};
use std::marker::PhantomData;

// #[predicate]
// fn abstract_dll(list: In<LinkedList<T>>, values: Seq<T>);

struct LinkedList {
    head: u32,
    tail: u32,
    data: PhantomData<u32>,
}

#[predicate]
fn dll(list: In<&LinkedList>, values: Seq<u32>) {
    assertion!(|head, tail| #(list -> LinkedList { head, tail, data: PhantomData }) * emp)
}

// #[predicate]
// fn abstract_linked_list(x: In<LinkedList>, y: Seq<i32>);

#[predicate]
fn new_linked_list(x: In<Option<u32>>) {
    assertion!(x == None);
    assertion!(x == Some(12))
}
