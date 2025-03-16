//@check-pass

// Imports
extern crate gilogic;

use gilogic::{fold, macros::*, unfold, Ownable};
use std::marker::PhantomData;
use std::ptr::NonNull;

// Difference with the paper:
// This file (list_std.rs) is executed in "noproph" mode, which corresponds to the verification of "type safety" only, not functional correctness
// (which requires prophecies to be enabled).
// In this mode, the `Ownable` trait does not require a second parameter which corresponds to the "pure representation" of the type.
// The existence of a noproph mode is mostly for demonstration purposes, and for legacy reasons.
// Please take a look at `tests/proph/list_std_proph.rs` for a version with prophecies (and representations) enabled (though with less comments).

// Structure definitions

// 0 modification on the structure definition, although since we copied it, the allocator API was added
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

// Note that these functions are not annotated with #[show_safety]
// That is because we do not give `Node<T>` an ownership predicate, and therefore, its safety cannot be directly verified.
// Node<T> is not a public structure, it cannot be re-used, and doesn't really carry any ownership invariant.
// It is simply an intermediate structure used for implementation.
// The safety of the LinkedList<T> is verified, and the safety of the Node<T> is indirectly verified through the safety of LinkedList<T>.
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

/*

    Visualisation of a doubly-linked list segment, in the non-empty case:

         head<-------|                                           tail
          |          |                                            |
          |       ---+------->|                                   |
          v       |  |        v                                   v
      |--------|  |  |   |--------|                           |--------|
      |        |  |  |   |        |                           |        |
      |  head  |  |  |   |   ...  |                           |  tail  |
      |  next  |->|  |   |   ...  |->                         |  next  |->
      |        |     |   |        |          .......          |        |
      |--------|     |   |--------|          .......          |--------|
      |        |     |   |        |          .......          |        |
  <---|  head  |     |<--|  head  |                        <--|  tail  |
      |  prev  |         |        |                           |  prev  |
      |        |         |        |                           |        |
      |--------|         |--------|                           |--------•
                      |                                                   |
                      -----------------------------------------------------
                          Recursively a doubly-linked list segement too
*/

// The doubly-linked-list segment predicate, explained in the paper's appendix
#[predicate]
fn dll_seg<T: Ownable>(
    // The `In<...>` annotation is used to specify that the argument is an "in-parameter" of the predicate,
    // as opposed to `len` which is an "out-parameter".
    // Ins- and outs- are specific to Gillian
    // For more details see "Matching Plans for Frame Inference in Compositional Reasoning", Lööw et al., ECOOP 2024
    head: In<Option<NonNull<Node<T>>>>, // Pointer to the head of the list
    tail_next: In<Option<NonNull<Node<T>>>>, // "next" field of the tail of the list
    tail: In<Option<NonNull<Node<T>>>>, // Pointer to the tail of the list
    head_prev: In<Option<NonNull<Node<T>>>>, // "prev" field of the head of the list
    len: usize,                         // Length of the list
) {
    // This predicate has two cases:
    // 1. The list is empty, in which case the length is 0
    assertion!((head == tail_next) * (tail == head_prev) * (len == 0));
    // 2. The list is non-empty, in which case
    //   - The length is positive
    //   - The head pointer is non-null
    //   - The head pointer points to a node with fields `next = head_next`,  `prev = head_prev` and `element`
    //   - The element is owned (i.e. its ownership predicate holds)
    //   - Recursively, there is a doubly-linked-list segment from `head_next` where
    //     * the `next` field of the tail is `tail_next
    //     * the tail is `tail`
    //     * the `prev` field of the head is `head`
    //     * the length is `len - 1`
    assertion!(|hptr, head_next, head_prev, element|
        (head == Some(hptr)) *
        (hptr -> Node { next: head_next, prev: head_prev, element }) *
        element.own() *
        dll_seg(head_next, tail_next, tail, head, len - 1) *
        (len > 0)
    )
}

// Extract lemma for the head of the list, according to section 4.3 of the paper.
// This lemma says that if we have a mutable reference to the list (where existentials `head`, `tail` and `len` have been frozen),
// then it is possible to extract the ownership of the *head element* of the list (i.e. `Ownable::own(&mut (*p.as_ptr()).element)`)
// This lemma manipulates higher-order logic terms that Gillian is not able to prove directly.
// Instead, Gillian proves another lemma that is *sufficient* for this lemma to hold.
// The Gillian-Rust compiler hence generates two lemmas:
// 1. A lemma called `extract_head____proof::<T>`, that is sufficient for `extract_head::<T>` to hold,
//    together with a simple proof
// 2. The lemma `extract_head::<T>`, marked as "trusted", as if the proof for the first lemma passes, this lemma holds.
#[extract_lemma(
    forall head, tail, len, p.
    assuming { head == Some(p) }
    from { list_ref_mut_htl(list, (head, tail, len)) }
    extract { Ownable::own(&mut (*p.as_ptr()).element) }
)]
fn extract_head<T: Ownable>(list: &mut LinkedList<T>);

// Alternative "view" of the `dll_seg` predicate, where the list
// is unfolded from right-to-left instead of left-to-right.
// Notice how here, we first take out the tail of the list, and then recursively use
// the `dll_seg_r` predicate, where `dll_seg` takes out the head first.
// We then define two lemmas `dll_seg_l_to_r` and `dll_seg_r_to_l` which, together
// show that `dll_seg <=> dll_seg_r`, and allow us to go from one view to the other.
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
        dll_seg_r(head, tail, tail_prev, head_prev, len - 1) *
        (len > 0)
    )
}

// Auxiliary lemma required to show that `dll_seg ==> dll_seg_r`
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
fn dll_seg_r_appened_left<T: Ownable>(
    x: Option<NonNull<Node<T>>>,
    next: Option<NonNull<Node<T>>>,
    tail_next: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
);

// Lemma that states that `dll_seg ==> dll_seg_r`, and transforms the lhs into the rhs
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

// Auxiliary lemma required to show that `dll_seg <== dll_seg_r`
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

// Auxiliary lemma required to show that `dll_seg <== dll_seg_r`
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

// Lemma that shows that `dll_seg <== dll_seg_r`, and transforms the rhs into the lhs
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

// Definition of the ownership predicate for the `LinkedList` structure
// The `with_freeze_lemma` automatically derives a lemma that allows us to "freeze" the existentials `head`, `tail` and `len`
// from the mutable reference.
// Specifically, the ownership predicate for `&mut LinkedList<T>(p)` is of the form
// `&(∃ head, tail, len. p -> { head, tail, len, ...} * ...)`
// and the derived lemma `freeze_htl` allows us to pull the existentials out of the full borrow
// (according to the Exists rule of the RustBelt lifetime logic) and obtain the predicate
// `list_ref_mut_htl::<T>(p) = ∃ head, tail, len. &(p -> { head, tail, len, ...} * ...)`
// This lemma is derived by the compiler on request, as it can be checked syntactically that it holds.
#[with_freeze_lemma(lemma_name = freeze_htl, predicate_name = list_ref_mut_htl, frozen_variables = [head, tail, len])]
impl<T: Ownable> Ownable for LinkedList<T> {
    #[predicate]
    fn own(self) {
        assertion!(|head: Option<NonNull<Node<T>>>,
                    tail: Option<NonNull<Node<T>>>,
                    len: usize,
                    p: Option<NonNull<Node<T>>>,
                    n: Option<NonNull<Node<T>>>| (self
            == LinkedList {
                head,
                tail,
                len,
                marker: PhantomData
            })
            * dll_seg(head, p, tail, n, len)
            * (p == None)
            * (n == None));
    }
}

impl<T: Ownable> LinkedList<T> {
    // the #[show_safety] attributes automatically derives a specification that shows that `new` is "safe".
    // It expands to something of the form:
    // #[specification(
    //    requires { emp }
    //    ensures { ret.own() }
    //  )]
    // The `expand.sh` script can be used to see the expanded form of the macro.
    #[show_safety]
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }

    // This function is not annotaded with #[show_safety], because we do not verify that, on its own, it is safe.
    // Instead, we verify that `push_back` is safe (as it is publicly exposed).
    // Because `push_back_node` does not have a specification, it is simply symbolically executed by Gillian when verifying `push_back`.
    fn push_back_node(&mut self, mut node: Box<Node<T>>) {
        unsafe {
            node.next = None;
            node.prev = self.tail;
            let node = Some(Box::leak(node).into());

            match self.tail {
                None => self.head = node,
                Some(tail) => (*tail.as_ptr()).next = node,
            }

            self.tail = node;
            self.len += 1;
        }
    }

    // Same as `push_back_node`.
    fn pop_back_node(&mut self) -> Option<Box<Node<T>>> {
        match self.tail {
            None => None,
            Some(node) => unsafe {
                let node = Box::from_raw(node.as_ptr());
                self.tail = node.prev;

                match self.tail {
                    None => self.head = None,
                    Some(tail) => (*tail.as_ptr()).next = None,
                }

                self.len -= 1;
                Some(node)
            },
        }
    }

    // Same as push_back_node and pop_back_node.
    fn pop_front_node(&mut self) -> Option<Box<Node<T>>> {
        // Original function uses map, but our compiler does not yet support closures.
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
        // Node::into_element and pop_front_node do not have specifications, and therefore they are
        // automatically inlined.
        self.pop_front_node().map(Node::into_element)
    }

    fn push_front_node(&mut self, mut node: Box<Node<T>>) {
        unsafe {
            node.next = self.head;
            node.prev = None;
            let node = Some(Box::leak(node).into());

            match self.head {
                None => self.tail = node,
                Some(head) => (*head.as_ptr()).prev = node,
            }

            self.head = node;
            self.len += 1;
        }
    }

    #[show_safety]
    pub fn pop_back(&mut self) -> Option<T> {
        // For pop_back, we need to access the last element of the list and remove it.
        // However, the shape of the `dll_seg` predicate, used in the ownership predicate of the list,
        // does not allow us to access the tail of the list directly.
        // Therefore, use the `dll_seg_l_to_r` lemma that transforms the `dll_seg` predicate into a `dll_seg_r` predicate,
        // which allows us to access the tail of the list.
        dll_seg_l_to_r(self.head, None, self.tail, None);
        let res = self.pop_back_node().map(Node::into_element);
        // After popping the last element, we need to transform the `dll_seg_r` predicate back into a `dll_seg` predicate
        // in order to re-establish the ownership invariant of the list.
        // Note that, at this point, `self.tail` has changed, since the last element has been removed.
        dll_seg_r_to_l(self.head, None, self.tail, None);
        res
    }

    #[show_safety]
    pub fn push_back(&mut self, elt: T) {
        // See comments for pop_back.
        dll_seg_l_to_r(self.head, None, self.tail, None);
        self.push_back_node(Box::new(Node::new(elt)));
        dll_seg_r_to_l(self.head, None, self.tail, None);
    }

    #[show_safety]
    pub fn push_front(&mut self, elt: T) {
        // push_front manipulates the head of the list, which is directly accessible using the dll_seg predicate,
        // Therefore, this verification is entirely automatic.
        self.push_front_node(Box::new(Node::new(elt)));
    }

    // This one uses both the `freeze_htl` lemma (see comments for the with_freeze_lemma attribute above),
    // and the `extract_head` lemma (see comments for the extract_lemma attribute above).
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
