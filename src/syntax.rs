use crate::common::{Name, NoDispOption, Spanned, ToDoc, Tree};
use pretty::{Doc, RcDoc};
use std::{
    fmt::Display,
    ops::{Deref, RangeInclusive},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgsWithTypeE<S> {
    pub(crate) args: ArgsE<S>,
    pub(crate) ty: Option<Box<TypeE<S>>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermE<S> {
    App(Box<TermE<S>>, ArgsWithTypeE<S>, S),
    Susp(Box<TermE<S>>, S),
    Var(Name, S),
    Coh(Tree<NoDispOption<Name>>, Box<TypeE<S>>, S),
    Include(Box<TermE<S>>, RangeInclusive<usize>, S),
    Comp(S),
    Id(S),
    Hole(S),
}

pub type SubE<S> = Vec<TermE<S>>;
pub type LabelE<S> = Tree<NoDispOption<TermE<S>>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArgsE<S> {
    Sub(Spanned<SubE<S>, S>),
    Label(Spanned<LabelE<S>, S>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeE<S> {
    Base(S),
    Arr(TermE<S>, Option<Box<TypeE<S>>>, TermE<S>, S),
    App(Box<TypeE<S>>, ArgsWithTypeE<S>, S),
    Susp(Box<TypeE<S>>, S),
    Hole(S),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CtxE<S> {
    Tree(Tree<NoDispOption<Name>>),
    Other(Vec<(Name, TypeE<S>)>),
}

impl<S> TermE<S> {
    pub(crate) fn span(&self) -> &S {
        match self {
            TermE::App(_, _, s)
            | TermE::Susp(_, s)
            | TermE::Var(_, s)
            | TermE::Coh(_, _, s)
            | TermE::Include(_, _, s)
            | TermE::Comp(s)
            | TermE::Hole(s)
            | TermE::Id(s) => s,
        }
    }
}

impl<S> TypeE<S> {
    pub(crate) fn span(&self) -> &S {
        match self {
            TypeE::Base(s)
            | TypeE::Arr(_, _, _, s)
            | TypeE::App(_, _, s)
            | TypeE::Susp(_, s)
            | TypeE::Hole(s) => s,
        }
    }
}

impl<S> ToDoc for ArgsWithTypeE<S> {
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

impl<S> ToDoc for TermE<S> {
    fn to_doc(&self) -> RcDoc<'_> {
        match self {
            TermE::App(t, a, _) => {
                RcDoc::group(t.to_doc().append(RcDoc::line_().append(a.to_doc()).nest(2)))
            }
            TermE::Susp(t, _) => RcDoc::group(
                RcDoc::text("Σ(")
                    .append(RcDoc::line_().append(t.to_doc()).nest(2))
                    .append(RcDoc::line_())
                    .append(")"),
            ),
            TermE::Var(t, _) => t.to_doc(),
            TermE::Coh(tr, ty, _) => RcDoc::group(
                RcDoc::text("coh [ ").append(tr.to_doc().nest(6)).append(
                    RcDoc::line()
                        .append(": ")
                        .append(ty.to_doc().nest(2))
                        .append(RcDoc::line().append("]"))
                        .nest(4),
                ),
            ),
            TermE::Include(tm, rng, _) => RcDoc::group(
                RcDoc::text(format!("inc<{}-{}>(", rng.start(), rng.end()))
                    .append(RcDoc::line_().append(tm.to_doc()).nest(2))
                    .append(RcDoc::line_().append(")")),
            ),
            TermE::Comp(_) => RcDoc::group(RcDoc::text("comp")),
            TermE::Hole(_) => RcDoc::group(RcDoc::text("_")),
            TermE::Id(_) => RcDoc::text("id"),
        }
    }
}

impl<S> Display for TermE<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(usize::MAX, f)
    }
}

impl<S> ToDoc for ArgsE<S> {
    fn to_doc(&self) -> RcDoc<'_> {
        match self {
            ArgsE::Sub(Spanned(args, _)) => RcDoc::group(
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
            ArgsE::Label(l) => {
                if l.0.is_max_tree() {
                    l.0.to_doc_max()
                } else {
                    l.to_doc()
                }
            }
        }
    }
}

impl<S> Display for ArgsE<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(usize::MAX, f)
    }
}

impl<S> ToDoc for TypeE<S> {
    fn to_doc(&self) -> RcDoc<'_> {
        match self {
            TypeE::Base(_) => RcDoc::text("*"),
            TypeE::Arr(s, a, t, _) => {
                let start = if let Some(x) = a {
                    x.to_doc().append(RcDoc::line()).append("| ")
                } else {
                    RcDoc::nil()
                };

                let end = RcDoc::group(
                    s.to_doc()
                        .append(RcDoc::line())
                        .append("→")
                        .append(RcDoc::line())
                        .append(t.to_doc()),
                );

                RcDoc::group(start.append(end))
            }
            TypeE::App(t, a, _) => RcDoc::group(
                RcDoc::text("(")
                    .append(t.to_doc())
                    .append(")")
                    .append(RcDoc::line_().append(a.to_doc()).nest(2)),
            ),
            TypeE::Susp(t, _) => RcDoc::group(
                RcDoc::text("Σ(")
                    .append(RcDoc::line_().append(t.to_doc()).nest(2))
                    .append(RcDoc::line_())
                    .append(")"),
            ),
            TypeE::Hole(_) => RcDoc::text("_"),
        }
    }
}

impl<S> Display for TypeE<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(usize::MAX, f)
    }
}

impl<S> Display for CtxE<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CtxE::Tree(t) => {
                t.fmt(f)?;
            }
            CtxE::Other(xs) => {
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
