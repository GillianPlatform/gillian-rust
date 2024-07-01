//@check-pass
//?gil:ignore
extern crate gilogic;

use gilogic::{
    macros::{assertion, predicate, specification, extract_lemma, prophecies::with_freeze_lemma_for_mutref},
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
    extract model mh: (T::RepresentationTy, T::RepresentationTy).
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

#[with_freeze_lemma_for_mutref(
    lemma_name = freeze_htl,
    predicate_name = list_ref_mut_htl,
    frozen_variables = [head, tail, len],
    inner_predicate_name = list_ref_mut_inner_htl
)]
impl<T: Ownable> Ownable for LinkedList<T> {
    type RepresentationTy = Seq<T::RepresentationTy>;

    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!(|head: Option<NonNull<Node<T>>>,
                    tail: Option<NonNull<Node<T>>>,
                    len: usize|
            (self == LinkedList {
                head,
                tail,
                len,
                marker: PhantomData
            })
            * (len == model.len())
            * dll_seg(head, None, tail, None, model))
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
    #[specification(
        requires { emp } 
        ensures  {  ret.own(Seq::nil()) }
    )]
    fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
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
    
    #[specification(forall current, proph.
        requires { self.own((current, proph)) }
        exists ret_repr.
        ensures { 
            ret.own(ret_repr) *
            $   ((current == Seq::empty()) && (proph == Seq::empty()) && (ret_repr == None))
             || (exists <
                    current_first: T::RepresentationTy,
                    current_rest: Seq<T::RepresentationTy>,
                    future_first: T::RepresentationTy,
                    future_rest: Seq<T::RepresentationTy>
                 >
                    (current == current_rest.prepend(current_first)) &&
                    (proph == future_rest.prepend(future_first)) &&
                    (ret_repr == Some((current_first, future_first))) &&
                    (future_rest == current_rest)
                )
            $
        }
    )]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        freeze_htl(self);
        match self.head.as_mut() {
            None => None,
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

    #[specification(forall current, proph.
        requires { self.own((current, proph)) }
        exists ret_repr.
        ensures { 
            ret.own(ret_repr) *
            $   ((current == Seq::empty()) && (proph == Seq::empty()) && (ret_repr == None))
             || ((current != Seq::empty()) && (proph == current.tail()) && (ret_repr == Some(current.head())))$ }
    )]
    pub fn pop_front(&mut self) -> Option<T> {
        // Original implementation uses map
        let res = match self.pop_front_node() {
            None => None,
            Some(node) => Some(node.into_element()),
        };
        mutref_auto_resolve!(self); // <- Unique thing added
        res
    }

    #[specification(forall current, proph, elt_repr.
        requires { self.own((current, proph)) * $current.len() < usize::MAX$ * elt.own(elt_repr) }
        ensures { ret.own(()) * $proph == current.prepend(elt_repr)$ }
    )]
    pub fn push_front(&mut self, elt: T) {
        self.push_front_node(Box::new(Node::new(elt)));
        mutref_auto_resolve!(self); // <- Unique thing added
    }

    // #[requires(|vdata: Seq<T>, vdll, vself| (self == vself) * (vself -> vdll) * vdll.shallow_repr(vdata) )]
    // #[ensures(|vself: &mut LinkedList<T>, vdata: Seq<T>, vdll|  (vself -> vdll) * (ret == vdata.len()) * vdll.shallow_repr(vdata))]
    // pub fn len(&self) -> usize {
    //     self.len
    // }
}
