extern crate gilogic;

use gilogic::macros::predicate;
use std::marker::PhantomData;
use std::ptr::NonNull;

pub struct LinkedList {
    head: Option<NonNull<Node>>,
    tail: Option<NonNull<Node>>,
    len: usize,
    marker: PhantomData<Box<Node>>,
}

struct Node {
    next: Option<NonNull<Node>>,
    prev: Option<NonNull<Node>>,
    element: u32,
}

#[predicate]
fn dll(x: In<LinkedList>, alpha: [u32]) {
    (alpha == [])
        * (x == LinkedList {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        })
}

impl LinkedList {
    #[requires(emp)]
    #[ensures(dll(ret, []))]
    fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }
}
