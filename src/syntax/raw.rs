use std::{
    fmt::Display,
    ops::{Deref, RangeInclusive},
};

use pretty::{Doc, RcDoc};

use crate::common::{Name, NoDispOption, Spanned, ToDoc, Tree};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgsWithTypeR<S> {
    pub(crate) args: ArgsR<S>,
    pub(crate) ty: Option<Box<TypeR<S>>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermR<S> {
    App(Box<TermR<S>>, ArgsWithTypeR<S>, S),
    Susp(Box<TermR<S>>, S),
    Var(Name, S),
    Coh(Tree<NoDispOption<Name>>, Box<TypeR<S>>, S),
    Include(Box<TermR<S>>, RangeInclusive<usize>, S),
    Comp(S),
    Id(S),
    Hole(S),
}

pub type SubR<S> = Vec<TermR<S>>;
pub type LabelR<S> = Tree<NoDispOption<TermR<S>>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArgsR<S> {
    Sub(Spanned<SubR<S>, S>),
    Label(Spanned<LabelR<S>, S>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeR<S> {
    Base(S),
    Arr(TermR<S>, Option<Box<TypeR<S>>>, TermR<S>, S),
    App(Box<TypeR<S>>, ArgsWithTypeR<S>, S),
    Susp(Box<TypeR<S>>, S),
    Hole(S),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CtxR<S> {
    Tree(Tree<NoDispOption<Name>>),
    Other(Vec<(Name, TypeR<S>)>),
}

impl<S> TermR<S> {
    pub(crate) fn span(&self) -> &S {
        match self {
            TermR::App(_, _, s)
            | TermR::Susp(_, s)
            | TermR::Var(_, s)
            | TermR::Coh(_, _, s)
            | TermR::Include(_, _, s)
            | TermR::Comp(s)
            | TermR::Hole(s)
            | TermR::Id(s) => s,
        }
    }
}

impl<S> TypeR<S> {
    pub(crate) fn span(&self) -> &S {
        match self {
            TypeR::Base(s)
            | TypeR::Arr(_, _, _, s)
            | TypeR::App(_, _, s)
            | TypeR::Susp(_, s)
            | TypeR::Hole(s) => s,
        }
    }
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
            TermR::App(t, a, _) => {
                RcDoc::group(t.to_doc().append(RcDoc::line_().append(a.to_doc()).nest(2)))
            }
            TermR::Susp(t, _) => RcDoc::group(
                RcDoc::text("Σ(")
                    .append(RcDoc::line_().append(t.to_doc()).nest(2))
                    .append(RcDoc::line_())
                    .append(")"),
            ),
            TermR::Var(t, _) => t.to_doc(),
            TermR::Coh(tr, ty, _) => RcDoc::group(
                RcDoc::text("coh [ ").append(tr.to_doc().nest(6)).append(
                    RcDoc::line()
                        .append(": ")
                        .append(ty.to_doc().nest(2))
                        .append(RcDoc::line().append("]"))
                        .nest(4),
                ),
            ),
            TermR::Include(tm, rng, _) => RcDoc::group(
                RcDoc::text(format!("inc<{}-{}>(", rng.start(), rng.end()))
                    .append(RcDoc::line_().append(tm.to_doc()).nest(2))
                    .append(RcDoc::line_().append(")")),
            ),
            TermR::Comp(_) => RcDoc::group(RcDoc::text("comp")),
            TermR::Hole(_) => RcDoc::group(RcDoc::text("_")),
            TermR::Id(_) => RcDoc::text("id"),
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
            TypeR::Base(_) => RcDoc::text("*"),
            TypeR::Arr(s, a, t, _) => {
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
            TypeR::App(t, a, _) => RcDoc::group(
                RcDoc::text("(")
                    .append(t.to_doc())
                    .append(")")
                    .append(RcDoc::line_().append(a.to_doc()).nest(2)),
            ),
            TypeR::Susp(t, _) => RcDoc::group(
                RcDoc::text("Σ(")
                    .append(RcDoc::line_().append(t.to_doc()).nest(2))
                    .append(RcDoc::line_())
                    .append(")"),
            ),
            TypeR::Hole(_) => RcDoc::text("_"),
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
