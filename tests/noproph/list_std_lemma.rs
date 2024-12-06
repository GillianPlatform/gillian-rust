//@check-pass
extern crate gilogic;

use gilogic::{macros::*, unfold, Ownable};
use std::marker::PhantomData;
use std::ptr::NonNull;

// 0 modification, although since I copied it, the allocator API was added
pub struct LinkedList<T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
    marker: PhantomData<Box<Node<T>>>,
}

struct Node<T> {
    next: Option<NonNull<Node<T>>>,
    prev: Option<NonNull<Node<T>>>,
    element: T,
}

#[predicate]
fn dll_seg<T: Ownable>(
    head: In<Option<NonNull<Node<T>>>>,
    tail_next: In<Option<NonNull<Node<T>>>>,
    tail: In<Option<NonNull<Node<T>>>>,
    head_prev: In<Option<NonNull<Node<T>>>>,
    len: usize,
) {
    assertion!((head == tail_next) * (tail == head_prev) * (len == 0));
    assertion!(|hptr, head_next, head_prev, element|
        (head == Some(hptr)) *
        (hptr -> Node { next: head_next, prev: head_prev, element }) *
        element.own() *
        dll_seg(head_next, tail_next, tail, head, len - 1)
    )
}

#[predicate]
fn dll_seg_r<T: Ownable>(
    head: In<Option<NonNull<Node<T>>>>,
    tail_next: In<Option<NonNull<Node<T>>>>,
    tail: In<Option<NonNull<Node<T>>>>,
    head_prev: In<Option<NonNull<Node<T>>>>,
    len: usize,
) {
    assertion!((head == tail_next) * (tail == head_prev) * (len == 0));
    assertion!(|tptr, tail_next, tail_prev, element|
        (tail == Some(tptr)) *
        (tptr -> Node { next: tail_next, prev: tail_prev, element }) *
        element.own() *
        dll_seg_r(head, tail, tail_prev, head_prev, len - 1)
    )
}

#[lemma]
#[specification(
     forall len.
     requires {
         dll_seg(head, tail_next, tail, head_prev, len)
     }
     ensures {
         dll_seg_r(head, tail_next, tail, head_prev, len)
     }
 )]
fn dll_seg_l_to_r<T: Ownable>(
    head: Option<NonNull<Node<T>>>,
    tail_next: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    head_prev: Option<NonNull<Node<T>>>,
) {
    // assert_bind!(len | dll_seg(head, tail_next, tail, head_prev, len));
    unfold!(dll_seg(head, tail_next, tail, head_prev, len));
}
