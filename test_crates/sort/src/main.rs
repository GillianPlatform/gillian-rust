use creusot_contracts::*;
use vec::{LinkedList, Vec};

use gilogic::prophecies::Ownable;
use {logic::ops::IndexLogic, snapshot, Snapshot};
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
#[ensures(sorted((^v)@))]
#[ensures((^v)@.permutation_of((*v)@))]
pub fn gnome_sort(v: &mut Vec<i32>) {
    let old_v = snapshot! { v };
    let mut i = 0;

    #[invariant(sorted_range(v@, 0, i@))]
    #[invariant(v@.permutation_of(old_v@))]
    while i < v.len() {
        let old_v = snapshot! { v };
        if i == 0 || *v.index_mut(i - 1) <= *v.index_mut(i) {
            i += 1;
        } else {
            proof_assert!(old_v@ == v@);
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
        popped = snapshot! { popped.push_back(i)};
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
    let _ = snapshot!(free_monoid::<i32>);
    let old_out = snapshot! { out };
    let old_l = snapshot! { l };
    let old_r = snapshot! { r };
    let a = l.pop_front();
    proof_assert!(match a {
        Some(x) => sorted(l@),
        None => true,
    });
    let b = r.pop_front();
    proof_assert!(match b {
        Some(x) => sorted(r@),
        None => true,
    });

    snapshot!(permut_frame_app::<i32>);
    snapshot!(permut_app::<i32>);

    match (a, b) {
        (Some(a), Some(b)) => {
            if a <= b {
                out.push_back(a);
                r.push_front(b);
                proof_assert!(forall<i : _> 0 <= i && i < l@.len() ==> a <= l@[i]);
                merge_aux(l, r, out)
            } else {
                proof_assert!(forall<i : _> 0 <= i && i < r@.len() ==> b <= r@[i]);
                out.push_back(b);
                l.push_front(a);
                merge_aux(r, l, out);
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
    proof_assert! { out@ == creusot_contracts::Seq::EMPTY };
    let _ = snapshot!(left_neutral::<i32>);
    merge_aux(l, r, &mut out);
    out
}
// Loads seq.FreeMonoid
#[trusted]
#[logic]
#[open(self)]
#[creusot::builtins = "seq.FreeMonoid.left_neutral"]
pub fn free_monoid<T>(s: Seq<T>) {
    dead
}

#[logic]
#[open(self)]
#[ensures(creusot_contracts::Seq::EMPTY.concat(s) == s)]
fn left_neutral<T>(s: Seq<T>) {}

#[logic]
#[open(self)]
#[ensures(s.push_back(t) == s.concat(Seq::singleton(t)))]
fn snoc_def<T>(s: Seq<T>, t: T) {}

#[logic]
#[open(self)]
#[requires(t.permutation_of(q))]
#[ensures(s.concat(t).permutation_of(s.concat(q)))]
pub fn permut_frame_app<T>(s: Seq<T>, t: Seq<T>, q: Seq<T>) {}

#[logic]
#[open(self)]
#[ensures(s.concat(t).permutation_of(t.concat(s)))]
pub fn permut_app<T>(s: Seq<T>, t: Seq<T>) {}

#[logic]
#[requires(s.permutation_of(t.concat(r)))]
#[ensures(s.push_back(e).permutation_of(t.concat(Seq::singleton(e).concat(r))))]
fn perm_right<T>(s: Seq<T>, t: Seq<T>, r: Seq<T>, e: T) {
    let _ = snoc_def::<T>;

    proof_assert!(t
        .concat(Seq::singleton(e).concat(r))
        .permutation_of(t.concat(r).push_back(e)));
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
        popped = snapshot! { popped.push_back(i)};
        snapshot!(perm_right::<i32>);

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

fn get_mut_client() {
    // We have desugared this, as the macro uses parts of Rust our frontend does not support yet.
    //let mut x = vec![100, 200, 300];
    let mut x = Vec::new();
    x.push(100);
    x.push(200);
    x.push(300);

    let xr = x.get_mut(1).unwrap();
    assert!(*xr == 200);
    *xr = 42;
    assert!(*x.get_mut(1).unwrap() == 42);
}
