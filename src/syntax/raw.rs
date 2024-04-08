use std::{
    fmt::Display,
    ops::{Deref, RangeInclusive},
};

use pretty::{Doc, RcDoc};

use crate::common::{Name, NoDispOption, Spanned, ToDoc, Tree};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgsWithTypeR<S> {
    pub(crate) args: ArgsR<S>,
    pub(crate) ty: Option<Box<TypeRS<S>>>,
}

pub type TermRS<S> = Spanned<TermR<S>, S>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermR<S> {
    App(Box<TermRS<S>>, ArgsWithTypeR<S>),
    Susp(Box<TermRS<S>>),
    Var(Name),
    Coh(Tree<NoDispOption<Name>>, Box<TypeRS<S>>),
    Include(Box<TermRS<S>>, RangeInclusive<usize>),
    Comp,
    Id,
    Hole,
}

pub type SubR<S> = Vec<TermRS<S>>;
pub type LabelR<S> = Tree<NoDispOption<TermRS<S>>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArgsR<S> {
    Sub(Spanned<SubR<S>, S>),
    Label(Spanned<LabelR<S>, S>),
}

pub type TypeRS<S> = Spanned<TypeR<S>, S>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeR<S> {
    Base,
    Arr(TermRS<S>, Option<Box<TypeRS<S>>>, TermRS<S>),
    App(Box<TypeRS<S>>, ArgsWithTypeR<S>),
    Susp(Box<TypeRS<S>>),
    Hole,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CtxR<S> {
    Tree(Tree<NoDispOption<Name>>),
    Other(Vec<(Name, TypeRS<S>)>),
}

impl<S> ToDoc for ArgsWithTypeR<S> {
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

impl<S> ToDoc for TermR<S> {
    fn to_doc(&self) -> RcDoc<'_> {
        match self {
            TermR::App(t, a) => {
                RcDoc::group(t.to_doc().append(RcDoc::line_().append(a.to_doc()).nest(2)))
            }
            TermR::Susp(t) => RcDoc::group(
                RcDoc::text("Σ(")
                    .append(RcDoc::line_().append(t.to_doc()).nest(2))
                    .append(RcDoc::line_())
                    .append(")"),
            ),
            TermR::Var(t) => t.to_doc(),
            TermR::Coh(tr, ty) => RcDoc::group(
                RcDoc::text("coh [ ").append(tr.to_doc().nest(6)).append(
                    RcDoc::line()
                        .append(": ")
                        .append(ty.to_doc().nest(2))
                        .append(RcDoc::line().append("]"))
                        .nest(4),
                ),
            ),
            TermR::Include(tm, rng) => RcDoc::group(
                RcDoc::text(format!("inc<{}-{}>(", rng.start(), rng.end()))
                    .append(RcDoc::line_().append(tm.to_doc()).nest(2))
                    .append(RcDoc::line_().append(")")),
            ),
            TermR::Comp => RcDoc::group(RcDoc::text("comp")),
            TermR::Hole => RcDoc::group(RcDoc::text("_")),
            TermR::Id => RcDoc::text("id"),
        }
    }
}

impl<S> Display for TermR<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(usize::MAX, f)
    }
}

impl<S> ToDoc for ArgsR<S> {
    fn to_doc(&self) -> RcDoc<'_> {
        match self {
            ArgsR::Sub(Spanned(args, _)) => RcDoc::group(
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
            ArgsR::Label(l) => {
                if l.0.is_max_tree() {
                    l.0.to_doc_max()
                } else {
                    l.to_doc()
                }
            }
        }
    }
}

impl<S> Display for ArgsR<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(usize::MAX, f)
    }
}

impl<S> ToDoc for TypeR<S> {
    fn to_doc(&self) -> RcDoc<'_> {
        match self {
            TypeR::Base => RcDoc::text("*"),
            TypeR::Arr(s, a, t) => {
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
            TypeR::App(t, a) => RcDoc::group(
                RcDoc::text("(")
                    .append(t.to_doc())
                    .append(")")
                    .append(RcDoc::line_().append(a.to_doc()).nest(2)),
            ),
            TypeR::Susp(t) => RcDoc::group(
                RcDoc::text("Σ(")
                    .append(RcDoc::line_().append(t.to_doc()).nest(2))
                    .append(RcDoc::line_())
                    .append(")"),
            ),
            TypeR::Hole => RcDoc::text("_"),
        }
    }
}

impl<S> Display for TypeR<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.to_doc().render_fmt(usize::MAX, f)
    }
}

impl<S> Display for CtxR<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CtxR::Tree(t) => {
                t.fmt(f)?;
            }
            CtxR::Other(xs) => {
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
            && self.elements.iter().all(|el| el.0.is_none())
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
