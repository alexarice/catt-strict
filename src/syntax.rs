use crate::common::{Name, NoDispOption, Spanned, ToDoc, Tree};
use pretty::{Doc, RcDoc};
use std::{
    fmt::Display,
    ops::{Deref, RangeInclusive},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgsWithType<S> {
    pub args: Args<S>,
    pub ty: Option<Box<Type<S>>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term<S> {
    App(Box<Term<S>>, ArgsWithType<S>, S),
    Susp(Box<Term<S>>, S),
    Var(Name, S),
    Coh(Tree<NoDispOption<Name>>, Box<Type<S>>, S),
    Include(Box<Term<S>>, RangeInclusive<usize>, S),
    UComp(S),
    Hole(S),
}

pub type Sub<S> = Vec<Term<S>>;
pub type Label<S> = Tree<NoDispOption<Term<S>>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Args<S> {
    Sub(Spanned<Sub<S>, S>),
    Label(Spanned<Label<S>, S>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<S> {
    Base(S),
    Arr(Term<S>, Option<Box<Type<S>>>, Term<S>, S),
    App(Box<Type<S>>, ArgsWithType<S>, S),
    Susp(Box<Type<S>>, S),
    Hole(S),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ctx<S> {
    Tree(Tree<NoDispOption<Name>>),
    Other(Vec<(Name, Type<S>)>),
}

impl<S> Term<S> {
    pub fn span(&self) -> &S {
        match self {
            Term::App(_, _, s)
            | Term::Susp(_, s)
            | Term::Var(_, s)
            | Term::Coh(_, _, s)
            | Term::Include(_, _, s)
            | Term::UComp(s)
            | Term::Hole(s) => s,
        }
    }
}

impl<S> Type<S> {
    pub fn span(&self) -> &S {
        match self {
            Type::Base(s)
            | Type::Arr(_, _, _, s)
            | Type::App(_, _, s)
            | Type::Susp(_, s)
            | Type::Hole(s) => s,
        }
    }
}

impl<S> ToDoc for ArgsWithType<S> {
    fn to_doc(&self) -> RcDoc<'_> {
        let ty_part = if let Some(ty) = &self.ty {
            RcDoc::line_()
                .append(RcDoc::group(
                    RcDoc::text("<")
                        .append(RcDoc::line_().append(ty.to_doc()))
                        .nest(2)
                        .append(RcDoc::line_())
                        .append(">"),
                ))
                .nest(2)
        } else {
            RcDoc::nil()
        };

        RcDoc::group(self.args.to_doc().append(ty_part))
    }
}

impl<S> ToDoc for Term<S> {
    fn to_doc(&self) -> RcDoc<'_> {
        match self {
            Term::App(t, a, _) => {
                RcDoc::group(t.to_doc().append(RcDoc::line_().append(a.to_doc()).nest(2)))
            }
            Term::Susp(t, _) => RcDoc::group(
                RcDoc::text("‼(")
                    .append(RcDoc::line_().append(t.to_doc()).nest(2))
                    .append(RcDoc::line_())
                    .append(")"),
            ),
            Term::Var(t, _) => t.to_doc(),
            Term::Coh(tr, ty, _) => RcDoc::group(
                RcDoc::text("coh [ ").append(tr.to_doc().nest(6)).append(
                    RcDoc::line()
                        .append(": ")
                        .append(ty.to_doc().nest(2))
                        .append(RcDoc::line().append("]"))
                        .nest(4),
                ),
            ),
            Term::Include(tm, rng, _) => RcDoc::group(
                RcDoc::text(format!("inc<{}-{}>(", rng.start(), rng.end()))
                    .append(RcDoc::line_().append(tm.to_doc()).nest(2))
                    .append(RcDoc::line_().append(")")),
            ),
            Term::UComp(_) => RcDoc::group(RcDoc::text("ucomp")),
            Term::Hole(_) => RcDoc::group(RcDoc::text("_")),
        }
    }
}

impl<S> Display for Term<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(usize::MAX, f)
    }
}

impl<S> ToDoc for Args<S> {
    fn to_doc(&self) -> RcDoc<'_> {
        match self {
            Args::Sub(Spanned(args, _)) => RcDoc::group(
                RcDoc::text("(")
                    .append(
                        RcDoc::intersperse(
                            args.iter().map(ToDoc::to_doc),
                            RcDoc::text(",").append(RcDoc::line()),
                        )
                        .nest(1),
                    )
                    .append(")"),
            ),
            Args::Label(l) => {
                if l.0.is_max_tree() {
                    l.0.to_doc_max()
                } else {
                    l.to_doc()
                }
            }
        }
    }
}

impl<S> Display for Args<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(usize::MAX, f)
    }
}

impl<S> ToDoc for Type<S> {
    fn to_doc(&self) -> RcDoc<'_> {
        match self {
            Type::Base(_) => RcDoc::text("*"),
            Type::Arr(s, a, t, _) => {
                let start = if let Some(x) = a {
                    x.to_doc().append(RcDoc::line()).append("| ")
                } else {
                    RcDoc::nil()
                };

                let end = RcDoc::group(
                    s.to_doc()
                        .append(RcDoc::line())
                        .append("->")
                        .append(RcDoc::line())
                        .append(t.to_doc()),
                );

                RcDoc::group(start.append(end))
            }
            Type::App(t, a, _) => RcDoc::group(
                RcDoc::text("(")
                    .append(t.to_doc())
                    .append(")")
                    .append(RcDoc::line_().append(a.to_doc()).nest(2)),
            ),
            Type::Susp(t, _) => RcDoc::group(
                RcDoc::text("‼(")
                    .append(RcDoc::line_().append(t.to_doc()).nest(2))
                    .append(RcDoc::line_())
                    .append(")"),
            ),
            Type::Hole(_) => RcDoc::text("_"),
        }
    }
}

impl<S> Display for Type<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(usize::MAX, f)
    }
}

impl<S> Display for Ctx<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ctx::Tree(t) => {
                t.fmt(f)?;
            }
            Ctx::Other(xs) => {
                for (name, ty) in xs {
                    write!(f, "({name} : {ty})")?;
                }
            }
        }
        Ok(())
    }
}

impl<T: ToDoc> Tree<NoDispOption<T>> {
    fn is_max_tree(&self) -> bool {
        !self.branches.is_empty()
            && self.elements.iter().all(|el| matches!(el.0, None))
            && self.branches.iter().all(Tree::is_max_tree_inner)
    }

    fn is_max_tree_inner(&self) -> bool {
        (self.branches.is_empty() && self.elements.first().unwrap().0.is_some())
            || self.is_max_tree()
    }

    fn to_doc_max(&self) -> RcDoc<'_> {
        if self.branches.is_empty() {
            self.elements.first().unwrap().0.as_ref().unwrap().to_doc()
        } else {
            RcDoc::group(
                RcDoc::text("[")
                    .append(RcDoc::line_().append(RcDoc::intersperse(
                        self.branches.iter().map(|br| br.to_doc_max()),
                        RcDoc::text(",").append(RcDoc::line_()),
                    )))
                    .nest(2)
                    .append(RcDoc::line_())
                    .append("]"),
            )
        }
    }
}

impl<T: ToDoc> ToDoc for Tree<NoDispOption<T>> {
    fn to_doc(&self) -> RcDoc<'_> {
        let mut iter = self.elements.iter();
        let mut inner = RcDoc::nil();

        if let Some(e) = iter.next() {
            let d = e.to_doc();
            if !matches!(d.deref(), Doc::Nil) {
                inner = inner.append(RcDoc::line_()).append(d);
            }
        }

        for (e, t) in iter.zip(&self.branches) {
            inner = inner.append(RcDoc::line_()).append(t.to_doc());
            let d = e.to_doc();
            if !matches!(d.deref(), Doc::Nil) {
                inner = inner.append(RcDoc::line_()).append(d);
            }
        }

        RcDoc::group(
            RcDoc::text("{")
                .append(inner.nest(1))
                .append(RcDoc::line_())
                .append("}"),
        )
    }
}

impl<T: Display> Display for Tree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        let mut iter = self.elements.iter();
        if let Some(e) = iter.next() {
            e.fmt(f)?;
        }
        for (e, t) in iter.zip(self.branches.iter()) {
            t.fmt(f)?;
            e.fmt(f)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}
