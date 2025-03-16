use gilogic::macros::{assertion, predicate};
use gilogic::mutref_auto_resolve;
use gilogic::prophecies::{Ownable, Prophecised};

struct EvenInt {
    num: i32,
}

impl Ownable for EvenInt {
    type RepresentationTy = i32;
    #[predicate]
    fn own(self, model: i32) {
        assertion!((self == EvenInt { num: model }) * (model % 2 == 0));
    }
}
