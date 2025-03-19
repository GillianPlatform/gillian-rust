use std::marker::PhantomData;

#[gillian::builtin]
#[rustc_diagnostic_item = "gillian::seq"]
pub struct Seq<T>(PhantomData<T>);

impl<T> Seq<T> {
    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::nil"]
    pub fn nil() -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::empty"]
    pub fn empty() -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::prepend"]
    pub fn prepend(self, _: T) -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::append"]
    pub fn push_back(self, _: T) -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::exchange"]
    pub fn exchange(self, _: Seq<T>, _: usize, _: usize) -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::concat"]
    pub fn concat(self, _: Self) -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::first"]
    pub fn first(self) -> T {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::last"]
    pub fn last(self) -> T {
        unreachable!()
    }

    #[allow(clippy::len_without_is_empty)]
    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::len"]
    pub fn len(self) -> usize {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::at"]
    pub fn at(self, _idx: usize) -> T {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::permutation_of"]
    pub fn permutation_of(self, _idx: Self) -> bool {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::sub"]
    pub fn subsequence(self, _start: usize, _size: usize) -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::repeat"]
    pub fn repeat(_x: T, _n: usize) -> Self {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::head"]
    pub fn head(self) -> T {
        unreachable!()
    }

    #[gillian::builtin]
    #[gillian::no_translate]
    #[rustc_diagnostic_item = "gillian::seq::tail"]
    pub fn tail(self) -> Self {
        unreachable!()
    }
}

impl<T> std::ops::Index<usize> for Seq<T> {
    type Output = T;

    #[rustc_diagnostic_item = "gillian::seq::index"]
    fn index(&self, _index: usize) -> &Self::Output {
        unreachable!()
    }
}
