extern crate gilogic;

use gilogic::{
    macros::{assertion, close_borrow, ensures, open_borrow, predicate, requires, show_safety},
    Ownable, Seq,
};
use std::marker::PhantomData;
use std::ptr::NonNull;

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

impl<T: Ownable> Node<T> {
    fn new(element: T) -> Self {
        Node {
            next: None,
            prev: None,
            element,
        }
    }
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

impl<T: Ownable> Ownable for LinkedList<T> {
    #[predicate]
    fn own(self) {
        assertion!(|head, tail, len| (self
            == LinkedList {
                head,
                tail,
                len,
                marker: PhantomData
            })
            * dll_seg(head, None, tail, None, len));
    }
}

impl<T: Ownable> LinkedList<T> {
    #[show_safety]
    fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }

    /// Adds the given node to the front of the list.
    #[requires(|e: T| self.own() * (node -> Node { next: None, prev: None, element: e }))]
    #[ensures(ret.own())]
    fn push_front_node(&mut self, mut node: Box<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            open_borrow!(self.own());
            node.next = self.head;
            node.prev = None;
            let node = Some(Box::leak(node).into());

            match self.head {
                None => self.tail = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(head) => (*head.as_ptr()).prev = node,
            }

            self.head = node;
            self.len += 1;
            close_borrow!(self.own());
        }
    }

    #[show_safety]
    pub fn push_front(&mut self, elt: T) {
        self.push_front_node(Box::new(Node::new(elt)));
    }

    // #[requires(|vdata: Seq<T>, vdll, vself| (self == vself) * (vself -> vdll) * vdll.shallow_repr(vdata) )]
    // #[ensures(|vself: &mut LinkedList<T>, vdata: Seq<T>, vdll|  (vself -> vdll) * (ret == vdata.len()) * vdll.shallow_repr(vdata))]
    // pub fn len(&self) -> usize {
    //     self.len
    // }
}
