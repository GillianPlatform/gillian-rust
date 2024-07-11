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
    (^out)@.permutation_of(out@.concat(l@).concat(r@))
)]
#[requires(sorted(l@))]
#[requires(sorted(r@))]
#[requires(sorted(out@))]
#[ensures(sorted((^out)@))]
#[requires(forall<i : _, j : _> 0 <= i && i < out@.len() ==> 0 <= j && j < l@.len() ==> out@[i] <= l@[j] )]
#[requires(forall<i : _, j : _> 0 <= i && i < out@.len() ==> 0 <= j && j < r@.len() ==> out@[i] <= r@[j] )]
fn merge_aux(l: &mut LinkedList<i32>, r: &mut LinkedList<i32>, out: &mut LinkedList<i32>) {
    let old_out = snapshot! { out };
    let old_l = snapshot! { l };
    let old_r = snapshot! { r };
    let a = l.pop_front();
    proof_assert!(sorted(l@));
    let b = r.pop_front();
    proof_assert!(sorted(r@));

    snapshot!(permut_frame_app::<i32>);
    snapshot!(permut_app::<i32>);
    snapshot!(permut_app2::<i32>);
    snapshot!(permut_push::<i32>);

    match (a, b) {
        (Some(a), Some(b)) => {
            if a <= b {
                out.push_back(a);
                r.push_front(b);

                merge_aux(l, r, out)
            } else {
                proof_assert!(forall<i : _> 0 <= i && i < r@.len() ==> b <= r@[i]);
                out.push_back(b);
                l.push_front(a);
                proof_assert!(l@.ext_eq(old_l@));
                merge_aux(r, l, out);
                proof_assert!(old_out@.concat(old_r@.concat(old_l@)).permutation_of(old_out@.concat(old_r@).concat(old_l@)));
                proof_assert!(out@.permutation_of(old_out@.concat(old_l@).concat(old_r@)));
            }
        }
        (None, Some(b)) => {
            r.push_front(b);
            extend(out, r);
            return;
        }
        (Some(a), None) => {
            l.push_front(a);
            extend(out, l);
            return;
        }
        _ => return (),
    }
}

#[requires(sorted(l@))]
#[requires(sorted(r@))]
#[ensures(sorted(result@))]
#[ensures(
    result@.permutation_of(l@.concat(r@))
)]
fn merge(l: &mut LinkedList<i32>, r: &mut LinkedList<i32>) -> LinkedList<i32> {
    let mut out = LinkedList::new();

    merge_aux(l, r, &mut out);
    out
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


#[logic]
#[open(self)]
#[requires(s.permutation_of(t))]
#[requires(q.permutation_of(r))]
#[ensures(s.concat(q).permutation_of(t.concat(r)))]
pub fn permut_app2<T>(s: Seq<T>, t: Seq<T>, q: Seq<T>,  r: Seq<T>) {

}

#[logic]
#[requires(s.permutation_of(t.concat(r)))]
#[ensures(s.push(e).permutation_of(Seq::singleton(e).concat(t).concat(r)))]
fn perm_left<T>(s: Seq<T>, t: Seq<T>, r: Seq<T>, e: T) {
    let _ = permut_push::<T>;
    let _ = permut_sym::<T>;
    let _ = permut_app2::<T>;

    proof_assert!(Seq::singleton(e).concat(t).concat(r).permutation_of(t.concat(r).push(e)));

}


#[logic]
#[requires(s.permutation_of(t.concat(r)))]
#[ensures(s.push(e).permutation_of(t.concat(Seq::singleton(e).concat(r))))]
fn perm_right<T>(s: Seq<T>, t: Seq<T>, r: Seq<T>, e: T) {
    let _ = permut_push::<T>;
    let _ = permut_sym::<T>;
    let _ = permut_app2::<T>;

    proof_assert!(t.concat(Seq::singleton(e).concat(r)).permutation_of(t.concat(r).push(e)));
}

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
        snapshot!(perm_right::<i32>);
        snapshot!(perm_left::<i32>);

        if push_left {
            left.push_front(i);
        } else {
            right.push_front(i);
        };
        push_left = !push_left;
    }

    (left, right)
}

#[predicate]
fn sorted_range<T: OrdLogic>(s: Seq<T>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i : Int, j : Int> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[predicate]
fn sorted<T: OrdLogic>(s: Seq<T>) -> bool {
    sorted_range(s, 0, s.len())
}

#[ensures(sorted((^l)@))]
#[ensures(l@.permutation_of((^l)@))]
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
