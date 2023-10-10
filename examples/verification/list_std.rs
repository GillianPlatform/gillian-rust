extern crate gilogic;

use gilogic::{macros::*, Ownable};
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

#[predicate]
fn option_box_node<T: Ownable>(x: In<Option<Box<Node<T>>>>) {
    assertion!((x == None));
    assertion!(|next, prev, element, p|
        (x == Some(p)) * (p -> Node { next, prev, element }) * element.own()
    )
}

impl<T> Node<T> {
    fn new(element: T) -> Self {
        Node {
            next: None,
            prev: None,
            element,
        }
    }

    fn into_element(self: Box<Self>) -> T {
        self.element
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

#[extract_lemma]
#[requires(|head: Option<NonNull<Node<T>>>, tail: Option<NonNull<Node<T>>>, p: NonNull<Node<T>>|
    list_ref_mut_ht(list, head, tail) * (head == Some(p))
)]
#[ensures(Ownable::own(&mut (*p.as_ptr()).element))]
fn extract_head<T: Ownable>(list: &mut LinkedList<T>);

#[with_freeze_lemma_for_mutref(
    lemma_name = freeze_ht,
    predicate_name = list_ref_mut_ht,
    frozen_variables = [head, tail],
)]
impl<T: Ownable> Ownable for LinkedList<T> {
    #[predicate]
    fn own(self) {
        assertion!(
            |head: Option<NonNull<Node<T>>>, tail: Option<NonNull<Node<T>>>, len: usize| (self
                == LinkedList {
                    head,
                    tail,
                    len,
                    marker: PhantomData
                })
                * dll_seg(head, None, tail, None, len)
        );
    }
}

impl<T: Ownable> LinkedList<T> {
    #[show_safety]
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }

    #[requires( self.own() )]
    #[ensures(option_box_node(ret))]
    fn pop_front_node(&mut self) -> Option<Box<Node<T>>> {
        // Original function uses map
        match self.head {
            None => None,
            Some(node) => unsafe {
                let node = Box::from_raw(node.as_ptr());
                self.head = node.next;

                match self.head {
                    None => self.tail = None,
                    // Not creating new mutable (unique!) references overlapping `element`.
                    Some(head) => (*head.as_ptr()).prev = None,
                }

                self.len -= 1;
                Some(node)
            },
        }
    }

    #[show_safety]
    pub fn pop_front(&mut self) -> Option<T> {
        // Original implementation uses map
        match self.pop_front_node() {
            None => None,
            Some(node) => Some(node.into_element()),
        }
    }

    /// Adds the given node to the front of the list.
    #[requires(|e: T| self.own() * (node -> Node { next: None, prev: None, element: e }))]
    #[ensures(ret.own())]
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

    #[show_safety]
    pub fn push_front(&mut self, elt: T) {
        self.push_front_node(Box::new(Node::new(elt)));
    }

    #[show_safety]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        freeze_ht(self);
        match self.head.as_mut() {
            None => None,
            Some(node) => unsafe {
                let ret = Some(&mut node.as_mut().element);
                extract_head(self);
                ret
            },
        }
    }

    // #[requires(|vdata: Seq<T>, vdll, vself| (self == vself) * (vself -> vdll) * vdll.shallow_repr(vdata) )]
    // #[ensures(|vself: &mut LinkedList<T>, vdata: Seq<T>, vdll|  (vself -> vdll) * (ret == vdata.len()) * vdll.shallow_repr(vdata))]
    // pub fn len(&self) -> usize {
    //     self.len
    // }
}
