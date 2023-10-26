extern crate gilogic;

use gilogic::{
    Seq,
    macros::{assertion, ensures, predicate, requires},
    mutref_auto_resolve,
    prophecies::{Ownable, Prophecised},
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
}

#[predicate]
fn dll_seg<T: Ownable>(
    head: In<Option<NonNull<Node<T>>>>,
    tail_next: In<Option<NonNull<Node<T>>>>,
    tail: In<Option<NonNull<Node<T>>>>,
    head_prev: In<Option<NonNull<Node<T>>>>,
    data: Seq<T::RepresentationTy>,
){
    assertion!((head == tail_next) * (tail == head_prev) * (data == Seq::nil()));
    assertion!(|hptr, head_next, head_prev, element, e_repr, rest: Seq<T::RepresentationTy>|
        (head == Some(hptr)) *
        (hptr -> Node { next: head_next, prev: head_prev, element }) *
        element.own(e_repr) *
        (data == rest.prepend(e_repr)) *
        dll_seg(head_next, tail_next, tail, head, rest)
    )
}

impl<T: Ownable> Ownable for LinkedList<T> {
    type RepresentationTy = Seq<T::RepresentationTy>;

    #[predicate]
    fn own(self, model: Self::RepresentationTy) {
        assertion!(|head, tail, len| (self
            == LinkedList {
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
    #[requires(emp)]
    #[ensures(ret.own(Seq::nil()))]
    fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }

    /// Adds the given node to the front of the list.
    #[requires(|elem: T, current: Seq<T::RepresentationTy>, proph: Seq<T::RepresentationTy>, new_v: T::RepresentationTy| 
        self.own((current, proph)) *
        (current.len() < usize::MAX) *
        (node -> Node { next: None, prev: None, element: elem}) *
        elem.own(new_v))]
    #[ensures(
        $proph == current.prepend(new_v)$
    )]
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
            mutref_auto_resolve!(self); // <- Unique thing added
        }
    }

    
    // #[requires(|current: Seq<T::RepresentationTy>, proph: Seq<T::RepresentationTy>, velem: T::RepresentationTy|
    //     self.own((current, proph)) * elt.own(velem) * (current.len() < usize::MAX)
    // )]
    #[requires(
        |current: Seq<T::RepresentationTy>,
         proph: Seq<T::RepresentationTy>,
         vec_repr_model: Seq<T::RepresentationTy>, usize_max_model: usize, elt_repr: T::RepresentationTy|
            self.own((current, proph)) *
            <LinkedList<T> as ShallowModel>::shallow_model(current, vec_repr_model) *
            <usize as ShallowModel>::shallow_model(usize::MAX, usize_max_model) *
            (vec_repr_model.len() < usize_max_model) *
            elt.own(elt_repr)
    )]
    #[ensures(|ret_v, vec_repr_model_proph| ret.own(ret_v) * <LinkedList<T> as ShallowModel>::shallow_model(proph, vec_repr_model_proph) *  $vec_repr_model_proph == vec_repr_model.prepend(elt_repr)$)]
    // #[ensures($proph == current.prepend(velem)$)]
    pub fn push_front(&mut self, elt: T) {
        self.push_front_node(Box::new(Node::new(elt)));
    }

    // #[requires(|vdata: Seq<T>, vdll, vself| (self == vself) * (vself -> vdll) * vdll.shallow_repr(vdata) )]
    // #[ensures(|vself: &mut LinkedList<T>, vdata: Seq<T>, vdll|  (vself -> vdll) * (ret == vdata.len()) * vdll.shallow_repr(vdata))]
    // pub fn len(&self) -> usize {
    //     self.len
    // }
}
