//@check-pass
extern crate gilogic;

use gilogic::{fold, macros::*, unfold, Ownable};
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
        (len > 0) *
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
        (len > 0) *
        (tail == Some(tptr)) *
        (tptr -> Node { next: tail_next, prev: tail_prev, element }) *
        element.own() *
        dll_seg_r(head, tail, tail_prev, head_prev, len - 1)
    )
}

#[lemma]
#[specification(
    forall ptr, next, prev, element, len.
    requires {
        (x == Some(ptr)) * (ptr -> Node { next, prev, element }) * element.own() *
        dll_seg_r(next, tail_next, tail, x, len)
    }
    ensures {
        dll_seg_r(x, tail_next, tail, prev, len + 1)
    }
)]
fn dll_seg_r_append_left<T: Ownable>(
    x: Option<NonNull<Node<T>>>,
    next: Option<NonNull<Node<T>>>,
    tail_next: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
) {
    unfold!(dll_seg_r(next, tail_next, tail, x, len));
    if len == 0 {
        fold!(dll_seg_r(x, tail_next, tail, prev, len + 1));
    } else {
        assert_bind!(tptr, tail_prev, ep |
            (tail == Some(tptr)) *
            (tptr -> Node { next: tail_next, prev: tail_prev, element: ep })
        );
        dll_seg_r_append_left(x, next, tail, tail_prev);
        fold!(dll_seg_r(x, tail_next, tail, prev, len + 1));
    }
}

#[lemma]
#[specification(
    forall ptr, next, element, len.
    requires {
        dll_seg(head, tail_next, tail, head_prev, len) *
        (tail_next == Some(ptr)) * (ptr -> Node { next, prev: tail, element }) * element.own()
    }
    ensures {
        dll_seg(head, next, tail_next, head_prev, len + 1)
    }
)]
fn dll_seg_append_right<T: Ownable>(
    head: Option<NonNull<Node<T>>>,
    tail_next: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    head_prev: Option<NonNull<Node<T>>>,
) {
    unfold!(dll_seg(head, tail_next, tail, head_prev, len));
    if len == 0 {
        fold!(dll_seg(head, next, tail_next, head_prev, len + 1));
    } else {
        assert_bind!(hptr, head_next, ep|
            (head == Some(hptr)) *
            (hptr -> Node { next: head_next, prev: head_prev, element: ep })
        );
        dll_seg_append_right(head_next, tail_next, tail, head);
        fold!(dll_seg(head, next, tail_next, head_prev, len + 1));
    }
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
    unfold!(dll_seg(head, tail_next, tail, head_prev, len));
    if len == 0 {
        fold!(dll_seg_r(head, tail_next, tail, head_prev, len));
    } else {
        assert_bind!(hptr, head_next, head_prev, element |
            (head == Some(hptr)) *
            (hptr -> Node { next: head_next, prev: head_prev, element})
        );
        dll_seg_l_to_r(head_next, tail_next, tail, head);
        dll_seg_r_append_left(head, head_next, tail_next, tail);
    }
}

#[lemma]
#[specification(
     forall len.
     requires {
         dll_seg_r(head, tail_next, tail, head_prev, len)
     }
     ensures {
         dll_seg(head, tail_next, tail, head_prev, len)
     }
 )]
fn dll_seg_r_to_l<T: Ownable>(
    head: Option<NonNull<Node<T>>>,
    tail_next: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    head_prev: Option<NonNull<Node<T>>>,
) {
    unfold!(dll_seg_r(head, tail_next, tail, head_prev, len));
    if len == 0 {
        fold!(dll_seg(head, tail_next, tail, head_prev, len));
    } else {
        assert_bind!(tptr, tail_prev, ep |
            (tail == Some(tptr)) *
            (tptr -> Node { next: tail_next, prev: tail_prev, element: ep })
        );
        dll_seg_r_to_l(head, tail, tail_prev, head_prev);
        dll_seg_append_right(head, tail, tail_prev, head_prev);
    }
}
