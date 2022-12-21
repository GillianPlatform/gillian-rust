extern crate gilogic;

use gilogic::{
    macros::{assertion, ensures, predicate, requires},
    Seq,
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

impl<T> Node<T> {
    fn new(element: T) -> Self {
        Node {
            next: None,
            prev: None,
            element,
        }
    }
}

#[predicate]
fn dll_seg<T>(
    head: In<Option<NonNull<Node<T>>>>,
    tail_next: In<Option<NonNull<Node<T>>>>,
    tail: In<Option<NonNull<Node<T>>>>,
    head_prev: In<Option<NonNull<Node<T>>>>,
    data: Seq<T>,
) {
    assertion!((head == tail_next) * (tail == head_prev) * (data == Seq::nil()));
    assertion!(|hptr, head_next, head_prev, element, rest: Seq<T>|
        (head == Some(hptr)) *
        #(hptr -> Node { next: head_next, prev: head_prev, element }) *
        (data == rest.prepend(element)) *
        dll_seg(head_next, tail_next, tail, head, rest)
    )
}

#[predicate]
fn dll<T>(linked_list: In<LinkedList<T>>, data: Seq<T>) {
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

impl<T> LinkedList<T> {
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
    #[requires(|vself, vnode, velem, vdata: Seq<T>, vdll| (self == vself) * (node == vnode) *
        #(vself -> vdll) * #(vnode -> Node { next: None, prev: None, element: velem}) *
        (vdata.len() < usize::MAX) *
        dll(vdll, vdata))]
    #[ensures(|vself: &mut LinkedList<T>, new_vdll, velem, vdata: Seq<T>| #(vself -> new_vdll) * dll(new_vdll, vdata.prepend(velem)))]
    fn push_front_node(&mut self, mut node: Box<Node<T>>) {
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

    #[requires(|vself, velem, vdata: Seq<T>, vdll| (self == vself) * (elt == velem) *
        #(vself -> vdll) * (vdata.len() < usize::MAX) *
        dll(vdll, vdata))]
    #[ensures(|vself: &mut LinkedList<T>, new_vdll, velem, vdata: Seq<T>| #(vself -> new_vdll) * dll(new_vdll, vdata.prepend(velem)))]
    pub fn push_front(&mut self, elt: T) {
        self.push_front_node(Box::new(Node::new(elt)));
    }

    #[requires(|vdata: Seq<T>, vdll, vself| (self == vself) * #(vself -> vdll) * dll(vdll, vdata) )]
    #[ensures(|vself: &mut LinkedList<T>, vdata: Seq<T>, vdll|  #(vself -> vdll) * (ret == vdata.len()) * dll(vdll, vdata))]
    pub fn len(&self) -> usize {
        self.len
    }
}
