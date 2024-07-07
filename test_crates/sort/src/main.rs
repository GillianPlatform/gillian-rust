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

#[ensures((^this)@ == (*this)@.concat(ext@))]
fn extend(this: &mut LinkedList<i32>, ext: &mut LinkedList<i32>) {
    let old_ext = snapshot!(ext);
    let old_this = snapshot!(this);
    let mut popped = snapshot! { Seq::EMPTY };
    #[invariant(popped.concat(ext@).ext_eq(old_ext@))]
    #[invariant(this@.ext_eq(old_this@.concat(*popped)))]
    while let Some(i) = ext.pop_front() {
        popped = snapshot! { popped.push(i)};
        this.push_back(i)
    }

    proof_assert!(this@.ext_eq(old_this@.concat(old_ext@)));
}

#[ensures(
    result@.permutation_of(l@.concat(r@))
)]
fn merge(l: &mut LinkedList<i32>, r: &mut LinkedList<i32>) -> LinkedList<i32> {
    let mut out = LinkedList::new();
    let orig_l = snapshot! { *l };
    let orig_r = snapshot! { *r };
    proof_assert!(out@ == Seq::EMPTY);
    #[invariant(out@.concat(l@).concat(r@).permutation_of(orig_l@.concat(orig_r@)))]
    loop {
        let old_out = snapshot! { out };
        let old_l = snapshot! { *l };
        let old_r = snapshot! { *r };
        snapshot!(permut_frame_app::<i32>);
        snapshot!(permut_frame_app_l::<i32>);
        snapshot!(permut_app::<i32>);
        snapshot!(permut_push::<i32>);
        snapshot!(permut_sym::<i32>);
        let a = l.pop_front();
        let b = r.pop_front();

        match (a, b) {
            (Some(a), Some(b)) => {
                proof_assert!(out@.concat(Seq::singleton(a).concat(l@)).concat(Seq::singleton(b).concat(r@)).permutation_of(old_out@.concat(old_l@).concat(old_r@)));
                proof_assert!(out@.concat(Seq::singleton(a)).concat(l@).concat(Seq::singleton(b)).concat(r@).permutation_of(out@.concat(Seq::singleton(a).concat(l@)).concat(Seq::singleton(b).concat(r@))));
                proof_assert!(out@.concat(Seq::singleton(a)).concat(Seq::singleton(b)).concat(l@).concat(r@).permutation_of(out@.concat(Seq::singleton(a).concat(l@)).concat(Seq::singleton(b).concat(r@))));
                if a <= b {
                    out.push_front(b);
                    out.push_front(a);
                    proof_assert!(out@.permutation_of(old_out@.concat(Seq::singleton(a)).concat(Seq::singleton(b))));
                } else {
                    out.push_front(a);
                    out.push_front(b);
                    proof_assert!(out@.permutation_of(old_out@.concat(Seq::singleton(a)).concat(Seq::singleton(b))));
                }
                proof_assert!(out@.concat(l@).concat(r@).permutation_of(old_out@.concat(old_l@).concat(old_r@)));
            }
            (None, Some(b)) => {
                out.push_front(b);
                proof_assert!(out@.concat(r@).permutation_of(old_out@.concat(old_r@)));
                extend(&mut out, r);
                return out;
            }
            (Some(a), None) => {
                out.push_front(a);
                proof_assert!(out@.concat(l@).permutation_of(old_out@.concat(old_l@)));
                extend(&mut out, l);
                return out;
            }
            _ => return out,
        }
    }
}

// Loads seq.FreeMonoid
#[trusted]
#[logic]
#[open(self)]
#[creusot::builtins = "seq.FreeMonoid.left_neutral"]
pub fn free_monoid<T>(s: Seq<T>) {
    absurd
}

#[logic]
#[open(self)]
#[requires(t.permutation_of(q))]
#[ensures(s.concat(t).permutation_of(s.concat(q)))]
pub fn permut_frame_app<T>(s: Seq<T>, t: Seq<T>, q: Seq<T>) {}

#[logic]
#[open(self)]
#[requires(s.permutation_of(t))]
#[ensures(s.concat(q).permutation_of(t.concat(q)))]
pub fn permut_frame_app_l<T>(s: Seq<T>, t: Seq<T>, q: Seq<T>) {}

#[logic]
#[open(self)]
#[ensures(s.concat(t).permutation_of(t.concat(s)))]
pub fn permut_app<T>(s: Seq<T>, t: Seq<T>) {}

#[logic]
#[open(self)]
#[requires(s.permutation_of(t))]
#[ensures(s.push(q).permutation_of(t.push(q)))]
pub fn permut_push<T>(s: Seq<T>, t: Seq<T>, q: T) {}

#[logic]
#[open(self)]
#[requires(s.permutation_of(t))]
#[ensures(t.permutation_of(s))]
pub fn permut_sym<T>(s: Seq<T>, t: Seq<T>) {}

// #[ensures(result.0@.concat(result.1@) == inp@)]
#[ensures((^inp)@ == Seq::EMPTY)]
#[ensures(inp@.permutation_of(result.0@.concat(result.1@)))]
fn split(inp: &mut LinkedList<i32>) -> (LinkedList<i32>, LinkedList<i32>) {
    let mut push_left = true;
    let old_inp = snapshot!(inp);
    let mut left = LinkedList::new();
    let mut right = LinkedList::new();
    let mut popped = snapshot! { Seq::EMPTY };

    #[invariant(popped.concat(inp@).ext_eq(old_inp@))]
    #[invariant(popped.permutation_of(left@.concat(right@)))]
    while let Some(i) = inp.pop_front() {
        popped = snapshot! { popped.push(i)};
        snapshot!(free_monoid(*popped));
        snapshot!(permut_frame_app::<i32>);
        snapshot!(permut_app::<i32>);
        snapshot!(permut_push::<i32>);
        proof_assert!(popped.concat(inp@).ext_eq(old_inp@));
        proof_assert!(popped.permutation_of(left@.concat(right@).push(i)));
        proof_assert!(Seq::singleton(i).concat(left@.concat(right@)).permutation_of(left@.concat(right@).push(i)));
        proof_assert!(left@.concat(Seq::singleton(i).concat(right@)).permutation_of(left@.concat(right@.concat(Seq::singleton(i)))));
        let old_left = snapshot!(left);
        let old_right = snapshot!(right);
        if push_left {
            left.push_front(i);
        } else {
            right.push_front(i);
        };
        push_left = !push_left;
    }

    (left, right)
}

pub fn merge_sort(l: &mut LinkedList<i32>) {
    if l.is_empty() {
        return;
    }

    let (mut left, mut right) = split(l);

    merge_sort(&mut left);
    merge_sort(&mut right);

    let mut out = merge(&mut left, &mut right);

    std::mem::swap(l, &mut out)
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
