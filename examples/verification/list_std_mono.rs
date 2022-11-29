extern crate gilogic;

use gilogic::{
    macros::{assertion, ensures, predicate, requires},
    Seq,
};
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
fn dll_seg(
    head: In<Option<NonNull<Node>>>,
    tail_next: In<Option<NonNull<Node>>>,
    tail: In<Option<NonNull<Node>>>,
    head_prev: In<Option<NonNull<Node>>>,
    data: Seq<u32>,
) {
    assertion!((head == tail_next) * (tail == head_prev) * (data == Seq::nil()));
    assertion!(|hptr, head_next, head_prev, element, rest: Seq<u32>|
        (head == Some(hptr)) *
        #(hptr -> Node { next: head_next, prev: head_prev, element }) *
        (data == rest.prepend(element)) *
        dll_seg(head_next, tail_next, tail, head, rest)
    )
}

#[predicate]
fn dll(linked_list: In<LinkedList>, data: Seq<u32>) {
    assertion!(|head, tail, len| (linked_list
        == LinkedList {
            head,
            tail,
            len,
            marker: PhantomData
        })
        * (len == data.len())
        * dll_seg(head, None, tail, None, data))
}

impl LinkedList {
    #[requires(emp)]
    #[ensures(dll(ret, Seq::nil()))]
    fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }
}
