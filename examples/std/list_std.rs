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

impl LinkedList {
    /// Adds the given node to the front of the list.
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

    pub fn push_front(&mut self, elt: u32) {
        self.push_front_node(Box::new(Node::new(elt)));
    }

    pub const fn new() -> Self {
        LinkedList {
            head: None,
            tail: None,
            len: 0,
            marker: PhantomData,
        }
    }
}

pub fn main() -> usize {
    let mut list = LinkedList::new();
    list.push_front(3);
    list.push_front(2);
    list.push_front(1);
    list.push_front(0);
    list.len // ENDSWITH: 4i
}
