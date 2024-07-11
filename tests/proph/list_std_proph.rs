//@check-pass
extern crate creusillian;
extern crate gilogic;

use gilogic::{
    macros::{
        assertion, extract_lemma, lemma, predicate, prophecies::with_freeze_lemma_for_mutref,
        specification,
    },
    mutref_auto_resolve,
    prophecies::{Ownable, Prophecised, Prophecy},
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

trait ShallowModel: Ownable {
    type ModelTy;

    fn shallow_model(self_: Self::RepresentationTy, v: Self::ModelTy) -> gilogic::RustAssertion;
}

impl ShallowModel for usize {
    type ModelTy = Self;

    #[predicate]
    fn shallow_model(self_: In<Self::RepresentationTy>, v: Self::ModelTy) {
        assertion!((self_ == v))
    }
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

#[extract_lemma(
    forall head, tail, len, p.
    model m.
    extract model mh.
    assuming { head == Some(p) }
    from { list_ref_mut_htl(list, m, head, tail, len) }
    extract { Ownable::own(&mut (*p.as_ptr()).element, mh) }
    prophecise { m.tail().prepend(mh) }
)]
fn extract_head<'a, T: Ownable>(list: &'a mut LinkedList<T>) -> Prophecy<T::RepresentationTy>;

#[predicate]
fn dll_seg<T: Ownable>(
    head: In<Option<NonNull<Node<T>>>>,
    tail_next: In<Option<NonNull<Node<T>>>>,
    tail: In<Option<NonNull<Node<T>>>>,
    head_prev: In<Option<NonNull<Node<T>>>>,
    data: Seq<T::RepresentationTy>,
) {
    assertion!((head == tail_next) * (tail == head_prev) * (data == Seq::nil()));
    assertion!(|hptr, head_next, head_prev, element, e_repr, rest: Seq<T::RepresentationTy>|
        (head == Some(hptr)) *
        (hptr -> Node { next: head_next, prev: head_prev, element }) *
        element.own(e_repr) *
        (data == rest.prepend(e_repr)) *
        dll_seg(head_next, tail_next, tail, head, rest)
    )
}

#[predicate]
fn dll_seg_r<T: Ownable>(
    head: In<Option<NonNull<Node<T>>>>,
    tail_next: In<Option<NonNull<Node<T>>>>,
    tail: In<Option<NonNull<Node<T>>>>,
    head_prev: In<Option<NonNull<Node<T>>>>,
    data: Seq<T::RepresentationTy>,
) {
    assertion!((head == tail_next) * (tail == head_prev) * (data == Seq::nil()));
    assertion!(|tptr, tail_next, tail_prev, element, e_repr, rest: Seq<T::RepresentationTy>|
        (tail == Some(tptr)) *
        (tptr -> Node { next: tail_next, prev: tail_prev, element }) *
        element.own(e_repr) *
        (data == rest.append(e_repr)) *
        dll_seg_r(head, tail, tail_prev, head_prev, rest)
    )
}

#[lemma]
#[gillian::trusted]
#[specification(
    forall ptr, next, prev, element, data, repr.
    requires {
        (x == Some(ptr)) * (ptr -> Node { next, prev, element }) * element.own(repr) *
        dll_seg_r(next, tail_next, tail, x, data)
    }
    ensures {
        dll_seg_r(x, tail_next, tail, prev, data.prepend(repr))
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
     forall data.
     requires {
         dll_seg(head, tail_next, tail, head_prev, data)
     }
     ensures {
         dll_seg_r(head, tail_next, tail, head_prev, data)
     }
 )]
fn dll_seg_l_to_r<T: Ownable>(
    head: Option<NonNull<Node<T>>>,
    tail_next: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    head_prev: Option<NonNull<Node<T>>>,
);

#[lemma]
#[gillian::trusted]
#[specification(
     forall data.
     requires {
         dll_seg_r(head, tail_next, tail, head_prev, data)
     }
     ensures {
         dll_seg(head, tail_next, tail, head_prev, data)
     }
 )]
fn dll_seg_r_to_l<T: Ownable>(
    head: Option<NonNull<Node<T>>>,
    tail_next: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    head_prev: Option<NonNull<Node<T>>>,
);

#[with_freeze_lemma_for_mutref(
    lemma_name = freeze_htl,
    predicate_name = list_ref_mut_htl,
    frozen_variables = [head, tail, len],
    inner_predicate_name = list_ref_mut_inner_htl,
    resolve_macro_name = auto_resolve_list_ref_mut_htl
)]
impl<T: Ownable> Ownable for LinkedList<T> {
    type RepresentationTy = Seq<T::RepresentationTy>;

    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!(
            |head: Option<NonNull<Node<T>>>, tail: Option<NonNull<Node<T>>>, len: usize| (self
                == LinkedList {
                    head,
                    tail,
                    len,
                    marker: PhantomData
                })
                * (len == model.len())
                * dll_seg(head, None, tail, None, model)
        )
    }
}

impl<T: Ownable> ShallowModel for LinkedList<T> {
    type ModelTy = Self::RepresentationTy;

    #[predicate]
    fn shallow_model(self_: In<Self::RepresentationTy>, v: Self::ModelTy) {
        assertion!((self_ == v))
    }
}

impl<T: Ownable> LinkedList<T> {
    #[creusillian::ensures(ret@ == Seq::nil())]
    fn new() -> Self {
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

    /// Removes and returns the node at the back of the list.
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

    // #[requires(ix.in_bounds(self@))]
    // #[ensures(ix.has_value(self@, *result))]
    // #[ensures(ix.has_value((^self)@, ^result))]
    // #[ensures(ix.resolve_elswhere(self@, (^self)@))]
    // #[ensures((^self)@.len() == self@.len())]
    // fn index_mut(&mut self, ix: I) -> &mut <Vec<T, A> as Index<I>>::Output;

    #[creusillian::ensures(match ret {
        None => ((*self@) == Seq::empty()) && ((^self@) == Seq::empty()),
        Some(head) =>
            ((*self@).at(0) == *head@)
            && ((^self@).at(0) == ^head@)
            && (forall < i: usize > (0 < i && i < (*self@).len()) ==> (*self@).at(i) == (^self@).at(i))
    })]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        freeze_htl(self);
        match self.head.as_mut() {
            None => {
                auto_resolve_list_ref_mut_htl!(self);
                None
            }
            Some(node) => unsafe {
                let ret = &mut node.as_mut().element;
                let proph = extract_head(self);
                Some(ret.with_prophecy(proph))
            },
        }
    }

    // Obtained by automatically translating the Creusot specification:
    //#[ensures(
    // if (self@ = Seq::EMPTY) {
    //    self^ = Seq::EMPTY && ret@ = None
    // } else {
    //    self^ = self@.tail() && ret@ = Some(self@.head())
    // }
    // )]

    // #[specification(forall current, proph.
    //     requires { self.own((current, proph)) }
    //     exists ret_repr.
    //     ensures {
    //         ret.own(ret_repr) *
    //         $   ((current == Seq::empty()) && (proph == Seq::empty()) && (ret_repr == None))
    //          || ((current != Seq::empty()) && (proph == current.tail()) && (ret_repr == Some(current.head())))$ }
    // )]
    #[creusillian::ensures(match ret {
        None => ((*self@) == Seq::empty()) && ((^self@) == Seq::empty()),
        Some(head) => ((^self@) == (*self@).tail()) && ((*self@).at(0) == head@)
    })]
    pub fn pop_front(&mut self) -> Option<T> {
        // Original implementation uses map
        let res = match self.pop_front_node() {
            None => None,
            Some(node) => Some(node.into_element()),
        };
        mutref_auto_resolve!(self); // <- Unique thing added
        res
    }

    #[creusillian::requires((*self@).len() < usize::MAX@)]
    #[creusillian::ensures((^self@) == (*self@).prepend(elt_repr))]
    pub fn push_front(&mut self, elt: T) {
        self.push_front_node(Box::new(Node::new(elt)));
        mutref_auto_resolve!(self); // <- Unique thing added
    }

    #[creusillian::ensures(match ret {
        None => ((*self@) == Seq::empty()) && ((^self@) == Seq::empty()),
        Some(last) => ((^self@) == (*self@).sub(0, (*self@).len() - 1)) && ((*self@).last() == last@)
     })]
    pub fn pop_back(&mut self) -> Option<T> {
        dll_seg_l_to_r(self.head, None, self.tail, None);
        let res = self.pop_back_node().map(Node::into_element);
        dll_seg_r_to_l(self.head, None, self.tail, None);
        mutref_auto_resolve!(self);
        res
    }

    #[creusillian::requires((*self@).len() < usize::MAX@)]
    #[creusillian::ensures((^self@) == (*self@).append(elt_repr))]
    pub fn push_back(&mut self, elt: T) {
        dll_seg_l_to_r(self.head, None, self.tail, None);
        self.push_back_node(Box::new(Node::new(elt)));
        dll_seg_r_to_l(self.head, None, self.tail, None);
        mutref_auto_resolve!(self);
    }
}
