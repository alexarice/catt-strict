use crate::common::{Name, NoDispOption, Spanned, Tree};
use chumsky::{prelude::*, text::keyword};
use itertools::Itertools;
use pretty::RcDoc;
use std::{
    fmt::Display,
    ops::{Range, RangeInclusive},
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
}

pub type Sub<S> = Vec<Term<S>>;
pub type Label<S> = Tree<Spanned<NoDispOption<Term<S>>, S>>;

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
            | Term::Include(_, _, s) => s,
        }
    }
}

impl<S> Type<S> {
    pub fn span(&self) -> &S {
        match self {
            Type::Base(s) | Type::Arr(_, _, _, s) | Type::App(_, _, s) | Type::Susp(_, s) => s,
        }
    }
}

fn tree<O: 'static, P>(el: P) -> impl Parser<char, Tree<O>, Error = Simple<char>> + Clone
where
    P: Parser<char, O, Error = Simple<char>> + Clone + 'static,
{
    recursive(move |tr| {
        el.clone()
            .map(|e| Tree {
                elements: vec![e],
                branches: vec![],
            })
            .then(tr.then(el).repeated())
            .delimited_by(just("("), just(")"))
            .foldl(|mut tree, (br, el)| {
                tree.elements.push(el);
                tree.branches.push(br);
                tree
            })
    })
}

pub fn ident() -> impl Parser<char, Name, Error = Simple<char>> + Clone {
    text::ident().try_map(|x, span| {
        if x == "coh" || x == "let" || x == "_" {
            Err(Simple::custom(
                span,
                format!("Identifier cannot be \"{x}\""),
            ))
        } else {
            Ok(Name(x))
        }
    })
}

fn atom<P>(term: P) -> impl Parser<char, Term<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, Term<Range<usize>>, Error = Simple<char>> + Clone + 'static,
{
    keyword("coh")
        .ignore_then(
            tree(ident().padded().or_not().map(NoDispOption))
                .padded()
                .then(just(":").ignore_then(ty_internal(term.clone()).padded()))
                .delimited_by(just("["), just("]"))
                .padded()
                .map_with_span(|(ctx, ty), sp| Term::Coh(ctx, Box::new(ty), sp)),
        )
        .or(ident().map_with_span(Term::Var))
        .or(just("‼")
            .ignore_then(term.padded().delimited_by(just("("), just(")")))
            .map_with_span(|t, sp| Term::Susp(Box::new(t), sp)))
}

fn args<P>(term: P) -> impl Parser<char, Args<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, Term<Range<usize>>, Error = Simple<char>> + Clone + 'static,
{
    term.clone()
        .padded()
        .separated_by(just(","))
        .at_least(1)
        .delimited_by(just("<"), just(">"))
        .map_with_span(Spanned)
        .map(Args::Sub)
        .or(tree(
            term.or_not()
                .map(NoDispOption)
                .map_with_span(Spanned)
                .padded(),
        )
        .map_with_span(Spanned)
        .map(Args::Label))
}

fn args_with_type<P>(
    term: P,
) -> impl Parser<char, ArgsWithType<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, Term<Range<usize>>, Error = Simple<char>> + Clone + 'static,
{
    args(term.clone())
        .then(
            ty_internal(term)
                .map(Box::new)
                .padded()
                .delimited_by(just("<"), just(">"))
                .or_not(),
        )
        .map(|(args, ty)| ArgsWithType { args, ty })
}

fn ty_internal<P>(term: P) -> impl Parser<char, Type<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, Term<Range<usize>>, Error = Simple<char>> + Clone,
{
    let arr = term
        .clone()
        .then(just("->").padded().ignore_then(term.clone()));

    just("*")
        .map_with_span(|_, sp| Type::Base(sp))
        .or(arr.map_with_span(|(s, t), sp| Type::Arr(s, None, t, sp)))
        .then(
            just("|")
                .padded()
                .ignore_then(
                    term.clone()
                        .padded()
                        .then(just("->").ignore_then(term.padded())),
                )
                .map_with_span(|x, sp| (x, sp))
                .repeated(),
        )
        .foldl(|a, ((s, t), sp)| Type::Arr(s, Some(Box::new(a)), t, sp))
}

fn ctx_internal<P>(term: P) -> impl Parser<char, Ctx<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, Term<Range<usize>>, Error = Simple<char>> + Clone,
{
    tree(ident().padded().or_not().map(NoDispOption))
        .map(Ctx::Tree)
        .or(ident()
            .padded()
            .then(just(":").ignore_then(ty_internal(term.clone()).padded()))
            .delimited_by(just("("), just(")"))
            .padded()
            .repeated()
            .at_least(1)
            .map(Ctx::Other))
}

pub fn term() -> impl Parser<char, Term<Range<usize>>, Error = Simple<char>> + Clone {
    recursive(|term| {
        atom(term.clone())
            .map_with_span(|t, sp| (t, sp.start()))
            .padded()
            .then(
                args_with_type(term.clone())
                    .padded()
                    .map_with_span(|a, sp| (a, sp.end()))
                    .repeated(),
            )
            .foldl(|(t, start), (a, end)| (Term::App(Box::new(t), a, start..end), start))
            .map(|(t, _)| t)
    })
}

pub fn ty() -> impl Parser<char, Type<Range<usize>>, Error = Simple<char>> {
    ty_internal(term())
}

pub fn ctx() -> impl Parser<char, Ctx<Range<usize>>, Error = Simple<char>> {
    ctx_internal(term())
}

pub trait ToDoc {
    fn to_doc(&self) -> RcDoc<'_>;
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

impl<S> Display for ArgsWithType<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.args.fmt(f)?;
        if let Some(typ) = &self.ty {
            write!(f, "<{}>", typ)?;
        }
        Ok(())
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
                RcDoc::text("coh [").append(tr.to_doc()).append(
                    RcDoc::line()
                        .append(": ")
                        .append(ty.to_doc().nest(2))
                        .append(RcDoc::line_().append("]"))
                        .nest(4),
                ),
            ),
            Term::Include(tm, rng, _) => RcDoc::group(
                RcDoc::text(format!("inc<{}-{}>(", rng.start(), rng.end()))
                    .append(RcDoc::line_().append(tm.to_doc()).nest(2))
                    .append(RcDoc::line_().append(")")),
            ),
        }
    }
}

impl<S> Display for Term<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::App(t, a, _) => {
                t.fmt(f)?;
                a.fmt(f)?;
            }
            Term::Susp(head, _) => {
                write!(f, "‼({head})")?;
            }
            Term::Var(x, _) => {
                x.fmt(f)?;
            }
            Term::Coh(ctx, ty, _) => {
                write!(f, "coh [{} : {}]", ctx, ty)?;
            }
            Term::Include(tm, rng, _) => {
                write!(f, "inc<{}-{}>({tm})", rng.start(), rng.end())?;
            }
        }
        Ok(())
    }
}

impl<S> ToDoc for Args<S> {
    fn to_doc(&self) -> RcDoc<'_> {
        match self {
            Args::Sub(Spanned(args, _)) => RcDoc::group(
                RcDoc::text("<")
                    .append(
                        RcDoc::intersperse(
                            args.iter().map(ToDoc::to_doc),
                            RcDoc::text(",").append(RcDoc::line()),
                        )
                        .nest(1),
                    )
                    .append(">"),
            ),
            Args::Label(l) => l.to_doc(),
        }
    }
}

impl<S> Display for Args<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Args::Sub(Spanned(args, _)) => {
                write!(f, "<{}>", args.iter().map(ToString::to_string).join(","))
            }
            Args::Label(Spanned(l, _)) => l.fmt(f),
        }
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
        }
    }
}

impl<S> Display for Type<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Base(_) => f.write_str("*"),
            Type::Arr(s, a, t, _) => match a {
                Some(a) => write!(f, "{a} | {s} -> {t}"),
                None => write!(f, "{s} -> {t}"),
            },
            Type::App(ty, args, _) => {
                write!(f, "({ty}){args}")
            }
            Type::Susp(ty, _) => {
                write!(f, "‼({ty})")
            }
        }
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

impl<T: ToDoc> ToDoc for Tree<T> {
    fn to_doc(&self) -> RcDoc<'_> {
        let mut iter = self.elements.iter();
        let mut inner = iter.next().unwrap().to_doc();

        for (e, t) in iter.zip(&self.branches) {
            inner = inner
                .append(RcDoc::line_())
                .append(t.to_doc())
                .append(RcDoc::line_())
                .append(e.to_doc());
        }

        RcDoc::group(
            RcDoc::text("(")
                .append(RcDoc::line_().append(inner).nest(2))
                .append(RcDoc::line_())
                .append(")"),
        )
    }
}

impl<T: Display> Display for Tree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        let mut iter = self.elements.iter();
        if let Some(e) = iter.next() {
            e.fmt(f)?;
        }
        for (e, t) in iter.zip(self.branches.iter()) {
            t.fmt(f)?;
            e.fmt(f)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}
