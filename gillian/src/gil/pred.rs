use std::fmt::Display;

use pretty::{DocAllocator, Pretty};

use super::{print_utils, Assertion, Formula, Type};

#[derive(Debug, Clone)]
pub struct Pred {
    pub name: String,
    pub num_params: usize,
    pub params: Vec<(String, Option<Type>)>,
    pub ins: Vec<usize>,
    pub definitions: Vec<Assertion>,
    pub pure: bool,
    pub abstract_: bool,
    pub facts: Vec<Formula>,
    pub guard: Option<Assertion>,
}

impl<'a, D: DocAllocator<'a>> Pretty<'a, D> for &'a Pred
where
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, ()> {
        let mut doc = allocator.nil();

        if self.abstract_ {
            doc = doc.append(allocator.text("abstract "));
        }
        if self.pure {
            doc = doc.append(allocator.text("pure "));
        }

        doc = doc
            .append(allocator.text("pred "))
            .append(print_utils::maybe_quoted(&self.name))
            .append(
                allocator
                    .intersperse(
                        self.params.iter().enumerate().map(|(i, (name, ty))| {
                            let mut arg = allocator.nil();

                            if self.ins.contains(&i) {
                                arg = arg.append("+");
                            }
                            if let Some(ty) = ty {
                                arg.append(allocator.text(format!("{}: {}", name, ty)))
                            } else {
                                arg.append(allocator.text(name))
                            }
                        }),
                        ", ",
                    )
                    .parens(),
            );

        if !self.definitions.is_empty() {
            doc = doc
                .append(":")
                .append(allocator.line())
                .append(allocator.intersperse(&*self.definitions, ", "))
                .nest(2);
        }
        doc = doc.append(";").append(allocator.line());

        if !self.facts.is_empty() {
            doc = doc.append("facts: ");

            doc = doc.append(allocator.intersperse(&*self.facts, " and "));
        }
        if let Some(guard) = &self.guard {
            doc = doc
                .append("guard:")
                .append(allocator.space())
                .append(guard)
                .append(";");
        }
        doc
    }
}

impl Display for Pred {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let alloc = pretty::Arena::new();
        self.pretty(&alloc).render_fmt(80, f)
    }
}
