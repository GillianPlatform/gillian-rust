use std::marker::PhantomData;

pub struct Seq<T>(PhantomData<T>);

impl<T> Seq<T> {
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::seq::nil"]
    pub fn nil() -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::seq::empty"]
    pub fn empty() -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::seq::prepend"]
    pub fn prepend(self, _: T) -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::seq::append"]
    pub fn append(self, _: T) -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::seq::concat"]
    pub fn concat(self, _: Self) -> Self {
        unreachable!()
    }

    #[allow(clippy::len_without_is_empty)]
    #[gillian::builtin]
    #[rustc_diagnostic_item = "gillian::seq::len"]
    pub fn len(self) -> usize {
        unreachable!()
    }
}
