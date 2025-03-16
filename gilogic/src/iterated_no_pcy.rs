use crate as gilogic;
use gilogic::macros::{assertion, lemma, predicate, specification};
use gilogic::seq::Seq;
use gilogic::Ownable;

#[predicate]
pub fn all_own<T: Ownable>(vs: In<Seq<T>>) {
    assertion!((vs == Seq::empty()));
    assertion!(|x: T, rest: Seq<T>| (vs == rest.append(x)) * x.own() * all_own(rest))
}

// #[lemma]
// #[gillian::trusted]
// #[specification(
//     requires { (a < vs.len()) * (b < vs.len()) * all_own(vs) }
//     exists vs_swapped.
//     ensures {
//         all_own(vs_swapped)
//       * (forall < i : usize >
//             (0 <= i && i < vs.len() && i != a && i != b) ==> (vs.at(i) == vs_swapped.at(i)))
//       * (vs.at(a) == vs_swapped.at(b))
//       * (vs.at(b) == vs_swapped.at(a))
//     }
// )]
// pub fn all_own_swap<T: Ownable>(vs: Seq<T>, a: usize, b: usize);
