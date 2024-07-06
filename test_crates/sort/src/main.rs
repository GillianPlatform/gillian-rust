use ::std::marker::PhantomData;

use creusot_contracts::*;
use vec::{LinkedList, Vec};

use gilogic::prophecies::Ownable;
use {logic::IndexLogic, snapshot, Snapshot};
fn main() {}

#[ensures((^str)@.len() >= len@ && (^str)@.len() >= (*str)@.len())]
#[ensures((^str)@.len() == len@ || (^str)@.len() == (*str)@.len())]
#[ensures(len@ <= (*str)@.len() ==> (^str)@.len() == (*str)@.len())]
#[ensures(len@ > (*str)@.len() ==> (^str)@.len() == len@)]
#[ensures(forall<i: _> 0 <= i && i < (*str)@.len() ==> (^str)@[i] == (*str)@[i])]
#[ensures(forall<i: _> (*str)@.len() <= i && i < len@ ==> (^str)@[i] == pad)]
fn right_pad<T: Copy + Ownable>(str: &mut Vec<T>, len: usize, pad: T) {
    let old_str = snapshot! { str };

    #[invariant(old_str@.len() <= str@.len())]
    #[invariant(old_str@.len() < len@ ==> str@.len() <= len@)]
    #[invariant(str@.len() > len@ ==> str@.len() == old_str@.len())]
    #[invariant(forall<i: _> 0 <= i && i < old_str@.len() ==> str@[i] == old_str@[i])]
    #[invariant(forall<i: _> old_str@.len() <= i && i < str@.len() ==> str@[i] == pad)]
    while str.len() < len {
        str.push(pad);
    }
}

#[requires(true)]
#[ensures(forall<i : _, j : _> 0 <= i && i < j && j < (*v)@.len() ==> (^v)@[i] <= (^v)@[j])]
#[ensures((^v)@.permutation_of((*v)@))]
pub fn gnome_sort(v: &mut Vec<i32>) {
    let old_v = snapshot! { v };
    let mut i = 0;
    #[invariant(^*old_v == ^v)]
    #[invariant(forall<k : _, j : _> 0 <= k && k < j && j < i@ ==> v@[k] <= v@[j])]
    #[invariant(v@.permutation_of(old_v@))]
    while i < v.len() {
        if i == 0 || *v.index_mut(i - 1) <= *v.index_mut(i) {
            i += 1;
        } else {
            // TODO
            v.swap(i - 1, i);
            i -= 1;
        }
    }
}

fn extend(this: &mut LinkedList<i32>, ext: &mut LinkedList<i32>) {
    while let Some(i) = ext.pop_front() {
        this.push_front(i)
    }
}

#[ensures(
    result@ == l@.concat(r@)
)]
fn merge(l: &mut LinkedList<i32>, r: &mut LinkedList<i32>) -> LinkedList<i32> {
    let mut out = LinkedList::new();
    loop {
        let a = l.pop_front();
        let b = r.pop_front();

        match (a, b) {
            (Some(a), Some(b)) => {
                if a <= b {
                    out.push_front(b);
                    out.push_front(a);
                } else {
                    out.push_front(a);
                    out.push_front(b);
                }
            }
            (None, _) => {
                extend(&mut out, r);
                return out;
            }
            (_, None) => {
                extend(&mut out, l);
                return out;
            }
        }
    }
}

#[ensures(result.0@.concat(result.1@) == inp@)]
#[ensures((^inp)@ == Seq::EMPTY)]
fn split(inp: &mut LinkedList<i32>) -> (LinkedList<i32>, LinkedList<i32>) {
    let mut push_left = true;

    let mut left = LinkedList::new();
    let mut right = LinkedList::new();

    while let Some(i) = inp.pop_front() {
        if push_left {
            left.push_front(i)
        } else {
            right.push_front(i)
        };
        push_left = !push_left;
    }

    (left, right)
}

#[requires(length@ == l@.len())]
fn merge_sort(l: &mut LinkedList<i32>, length: usize) {
    if length >= 2 {
        let new_l = length / 2;
        let (mut left, mut right) = split(l);

        merge_sort(&mut left, new_l);
        merge_sort(&mut right, new_l);

        let mut out = merge(&mut left, &mut right);

        std::mem::swap(l, &mut out)
    }
}
// fn merge_sort(l : &mut LinkedList<i32>, length: usize) {
//     if length == 2 {
//         let a = l.pop_front().unwrap();
//         let b = l.pop_front().unwrap();

//         if a <= b {
//             l.push_front(b);
//             l.push_front(a);
//         } else {
//             l.push_front(a);
//             l.push_front(b);
//         }

//     } else if length == 3 {
//         let a = l.pop_front().unwrap();
//         let b = l.pop_front().unwrap();
//         let c = l.pop_front().unwrap();

//         if a <= b {
//             if b <= c {

//             } else if a <= c {

//             } else {

//             }
//         } else {
//             if a <= c {

//             } else if b <= c {

//             } else {

//             }
//         }
//     } else {

//     }
// }
