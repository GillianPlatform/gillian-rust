//@check-pass
extern crate gilogic;

use gilogic::{
    macros::{no_prophecies::with_freeze_lemma_for_mutref, *},
    Ownable,
    assert_bind, unfold,
};
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

#[extract_lemma(
    forall head, tail, len, p.
    assuming { head == Some(p) }
    from { list_ref_mut_htl(list, head, tail, len) }
    extract { Ownable::own(&mut (*p.as_ptr()).element) }
)]
fn extract_head<T: Ownable>(list: &mut LinkedList<T>);

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
#[gillian::trusted]
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
fn dll_seg_r_appened_left<T: Ownable>(
    x: Option<NonNull<Node<T>>>,
    next: Option<NonNull<Node<T>>>,
    tail_next: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
);


#[lemma]
#[gillian::trusted]
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
)
// {
//     if len == 0 {} else {
//         assert_bind!(len | dll_seg(head, tail_next, tail, head_prev, len));
//         if (len == 0) {} else {

//         }
//     }
// }

#[lemma]
#[gillian::trusted]
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
);



#[with_freeze_lemma_for_mutref(lemma_name = freeze_htl, predicate_name = list_ref_mut_htl, frozen_variables = [head, tail, len])]
impl<T: Ownable> Ownable for LinkedList<T> {
    #[predicate]
    fn own(self) {
        assertion!(|head: Option<NonNull<Node<T>>>, tail: Option<NonNull<Node<T>>>, len: usize,
                    p: Option<NonNull<Node<T>>>, n: Option<NonNull<Node<T>>>|
            (self == LinkedList { head, tail, len, marker: PhantomData })
            * dll_seg(head, p, tail, n, len) * (p == None) * (n == None));
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
    
    fn push_back_node(&mut self, mut node: Box<Node<T>>) {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        unsafe {
            node.next = None;
            node.prev = self.tail;
            let node = Some(Box::leak(node).into());

            match self.tail {
                None => self.head = node,
                // Not creating new mutable (unique!) references overlapping `element`.
                Some(tail) => (*tail.as_ptr()).next = node,
            }

            self.tail = node;
            self.len += 1;
        }
    }
    
    fn pop_back_node(&mut self) -> Option<Box<Node<T>>> {
        // This method takes care not to create mutable references to whole nodes,
        // to maintain validity of aliasing pointers into `element`.
        match self.tail {
            None => None,
            Some(node) => unsafe {
                let node = Box::from_raw(node.as_ptr());
                self.tail = node.prev;

                match self.tail {
                    None => self.head = None,
                    // Not creating new mutable (unique!) references overlapping `element`.
                    Some(tail) => (*tail.as_ptr()).next = None,
                }

                self.len -= 1;
                Some(node)
            },
        }
    }

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
        self.pop_front_node().map(Node::into_element)
    }

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
    pub fn pop_back(&mut self) -> Option<T> {
        dll_seg_l_to_r(self.head, None, self.tail, None);
        let res = self.pop_back_node().map(Node::into_element);
        dll_seg_r_to_l(self.head, None, self.tail, None);
        res
    }

    #[show_safety]
    pub fn push_back(&mut self, elt: T) {
        dll_seg_l_to_r(self.head, None, self.tail, None);
        self.push_back_node(Box::new(Node::new(elt)));
        dll_seg_r_to_l(self.head, None, self.tail, None);
    }

    #[show_safety]
    pub fn push_front(&mut self, elt: T) {
        self.push_front_node(Box::new(Node::new(elt)));
    }

    #[show_safety]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        freeze_htl(self);
        match self.head.as_mut() {
            None => None,
            Some(node) => unsafe {
                let ret = Some(&mut node.as_mut().element);
                extract_head(self);
                ret
            },
        }
    }

}