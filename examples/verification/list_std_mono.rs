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

impl Node {
    fn new(element: u32) -> Self {
        Node {
            next: None,
            prev: None,
            element,
        }
    }
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
        (hptr -> Node { next: head_next, prev: head_prev, element }) *
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

    /// Adds the given node to the front of the list.
    #[requires(|vself, vnode, velem, vdata, vdll| (self == vself) * (node == vnode) *
        (vself -> vdll) * (vnode -> Node { next: None, prev: None, element: velem}) *
        dll(vdll, vdata) *
        (vdata.len() < usize::MAX))]
    #[ensures(|vself: &mut LinkedList, new_vdll, velem, vdata: Seq<u32>| (vself -> new_vdll) * dll(new_vdll, vdata.prepend(velem)))]
    fn push_front_node(&mut self, mut node: Box<Node>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
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
        }
    }

    #[requires(|vself, velem, vdata: Seq<u32>, vdll| (self == vself) * (elt == velem) *
        (vself -> vdll) * (vdata.len() < usize::MAX) *
        (u32::MIN <= elt) * (elt <= u32::MAX) *
        dll(vdll, vdata))]
    #[ensures(|vself: &mut LinkedList, new_vdll, velem, vdata: Seq<u32>| (vself -> new_vdll) * dll(new_vdll, vdata.prepend(velem)))]
    pub fn push_front(&mut self, elt: u32) {
        self.push_front_node(Box::new(Node::new(elt)));
    }
}
