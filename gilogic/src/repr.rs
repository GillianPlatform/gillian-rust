use super::RustAssertion;

pub trait ShallowRepresentation {
    type ShallowModelTy;

    fn shallow_repr(self, model: Self::ShallowModelTy) -> RustAssertion;
}
