use crate as gilogic;
use gilogic::macros::{assertion, lemma, predicate, specification};
use gilogic::prophecies::*;
use gilogic::seq::Seq;

#[predicate]
pub fn all_own<T: Ownable>(vs: In<Seq<T>>, reprs: Seq<T::RepresentationTy>) {
    assertion!((vs == Seq::empty()) * (reprs == Seq::empty()));
    assertion!(|x: T,
                x_repr: T::RepresentationTy,
                rest: Seq<T>,
                rest_repr: Seq<T::RepresentationTy>| (vs == rest.push_back(x))
        * x.own(x_repr)
        * all_own(rest, rest_repr)
        * (reprs == rest_repr.push_back(x_repr)))
}

// #[lemma]
// #[gillian::trusted]
// #[specification(
//     forall reprs.
//     requires { (a < vs.len()) * (b < vs.len()) * all_own(vs, reprs) }
//     exists vs_swapped, reprs_swapped.
//     ensures {
//         all_own(vs_swapped, reprs_swapped)
//       * (forall < i : usize >
//             (0 <= i && i < vs.len() && i != a && i != b) ==>
//             (vs.at(i) == vs_swapped.at(i) && reprs.at(i) == reprs_swapped.at(i)))
//       * (vs.at(a) == vs_swapped.at(b))
//       * (vs.at(b) == vs_swapped.at(a))
//       * (reprs.at(a) == reprs_swapped.at(b))
//       * (reprs.at(b) == reprs_swapped.at(a))
//     }
// )]
// pub fn all_own_swap<T: Ownable>(vs: Seq<T>, a: usize, b: usize);
