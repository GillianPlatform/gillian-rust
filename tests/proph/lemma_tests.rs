//@check-pass
extern crate gilogic;


use gilogic::{
    macros::{assertion, predicate, specification, lemma, extract_lemma, prophecies::with_freeze_lemma_for_mutref},
    mutref_auto_resolve,
    prophecies::{Ownable, Prophecised, Prophecy},
    Seq,
};
use std::marker::PhantomData;
use std::ptr::NonNull;

// Commit hash from stdlib: 

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
) { 
}

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
