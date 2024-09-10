use pretty::{DocAllocator, Pretty};

use super::{print_utils, Assertion};
use std::fmt;

#[derive(Debug)]
pub enum Flag {
    Normal,
    Error,
}

impl fmt::Display for Flag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Flag::Normal => write!(f, "normal"),
            Flag::Error => write!(f, "error"),
        }
    }
}

#[derive(Debug)]
pub struct SingleSpec {
    pub pre: Assertion,
    pub posts: Vec<Assertion>,
    pub flag: Flag,
    pub trusted: bool,
}

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for &'a SingleSpec
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        let mut doc = alloc.nil();

        if self.trusted {
            doc = doc.append(alloc.text("trusted").append(alloc.hardline()));
        }

        doc = doc.append(self.pre.pretty(alloc).nest(2).enclose("[[ ", " ]]")).append(alloc.hardline());

        let posts_doc = alloc.intersperse(
            self.posts.iter().map(|p| p.pretty(alloc)),
            alloc.text(";").append(alloc.hardline()),
        );

        doc = doc
            .append(posts_doc.nest(2).enclose("[[ ", " ]]"))
            .append(alloc.hardline());

        doc = doc.append(alloc.text(self.flag.to_string()));

        doc.group()
    }
}
impl fmt::Display for SingleSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alloc = pretty::Arena::new();
        self.pretty(&alloc).render_fmt(80, f)
    }
}

#[derive(Debug)]
pub struct Spec {
    pub name: String,
    pub params: Vec<String>,
    pub sspecs: Vec<SingleSpec>,
}

impl fmt::Display for Spec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alloc = pretty::Arena::new();
        self.pretty(&alloc).render_fmt(80, f)
    }
}

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for &'a Spec
where
    D::Doc: Clone,
{
    fn pretty(self, alloc: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        let header = alloc
            .text("spec ")
            .append(print_utils::maybe_quoted(&self.name))
            .append(alloc.text("("))
            .append(alloc.intersperse(self.params.iter().map(|p| alloc.text(p)), alloc.text(", ")))
            .append(alloc.text(")"))
            .group();

        let body = alloc.intersperse(
            self.sspecs.iter().map(|s| s.pretty(alloc)),
            alloc.hardline().append(alloc.text(";")),
        );

        header.append(alloc.hardline()).append(body).group()
    }
}
