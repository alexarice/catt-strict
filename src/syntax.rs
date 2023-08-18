use chumsky::{prelude::*, text::keyword};
use itertools::Itertools;
use std::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Name(String);

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NoDispOption<T>(pub Option<T>);

impl<T: Display> Display for NoDispOption<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            Some(e) => e.fmt(f),
            None => Ok(()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    App(Box<Term>, Args, Option<Box<Type>>),
    Var(Name),
    Coh(Ctx, Box<Type>),
    Meta,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Args {
    Sub(Vec<Term>),
    Label(Tree<NoDispOption<Term>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Meta,
    Base,
    Arr(Term, Option<Box<Type>>, Term),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ctx {
    Tree(Tree<NoDispOption<Name>>),
    Other(Vec<(Name, Option<Type>)>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tree<T> {
    pub elements: Vec<T>,
    pub branches: Vec<Tree<T>>,
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

fn ident() -> impl Parser<char, Name, Error = Simple<char>> + Clone {
    text::ident().padded().try_map(|x, span| {
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

fn atom<P>(term: P) -> impl Parser<char, Term, Error = Simple<char>> + Clone
where
    P: Parser<char, Term, Error = Simple<char>> + Clone,
{
    keyword("coh")
        .ignore_then(
            ctx(term.clone())
                .padded()
                .then(just(":").ignore_then(ty(term).padded()))
                .delimited_by(just("["), just("]"))
                .padded()
                .map(|(ctx, ty)| Term::Coh(ctx, Box::new(ty))),
        )
        .or(ident().map(|x| Term::Var(x)))
        .or(just("_").to(Term::Meta))
}

fn args<P>(term: P) -> impl Parser<char, Args, Error = Simple<char>> + Clone
where
    P: Parser<char, Term, Error = Simple<char>> + Clone + 'static,
{
    term.clone()
        .padded()
        .separated_by(just(","))
        .at_least(1)
        .delimited_by(just("("), just(")"))
        .map(Args::Sub)
        .or(tree(term.or_not().map(NoDispOption).padded()).map(Args::Label))
}

fn ty<P>(term: P) -> impl Parser<char, Type, Error = Simple<char>> + Clone
where
    P: Parser<char, Term, Error = Simple<char>> + Clone,
{
    let arr = term
        .clone()
        .then(just("->").padded().ignore_then(term.clone()));

    just("_")
        .to(Type::Meta)
        .or(just("*").to(Type::Base))
        .or(arr.map(|(s, t)| Type::Arr(s, None, t)))
        .then(
            just("|")
                .padded()
                .ignore_then(
                    term.clone()
                        .padded()
                        .then(just("->").ignore_then(term.padded())),
                )
                .repeated(),
        )
        .foldl(|a, (s, t)| Type::Arr(s, Some(Box::new(a)), t))
}

fn ctx<P>(term: P) -> impl Parser<char, Ctx, Error = Simple<char>> + Clone
where
    P: Parser<char, Term, Error = Simple<char>> + Clone,
{
    tree(ident().padded().or_not().map(NoDispOption))
        .map(Ctx::Tree)
        .or(ident()
            .map(|i| (i, None))
            .or(ident().padded().then(
                just(":")
                    .ignore_then(ty(term).padded().map(Some))
                    .delimited_by(just("("), just(")")),
            ))
            .repeated()
            .map(Ctx::Other))
}

pub fn term() -> impl Parser<char, Term, Error = Simple<char>> + Clone {
    recursive(|term| {
        atom(term.clone())
            .padded()
            .then(
                args(term.clone())
                    .then(
                        ty(term)
                            .padded()
                            .delimited_by(just("<"), just(">"))
                            .or_not(),
                    )
                    .padded()
                    .repeated(),
            )
            .foldl(|t, (a, ty)| Term::App(Box::new(t), a, ty.map(Box::new)))
    })
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Meta => {
                f.write_str("_")?;
            }
            Term::App(t, a, ty) => {
                t.fmt(f)?;
                a.fmt(f)?;
                if let Some(typ) = ty {
                    write!(f, "<{}>", typ)?;
                }
            }
            Term::Var(name) => {
                name.0.fmt(f)?;
            }
            Term::Coh(ctx, ty) => {
                write!(f, "coh [{} : {}]", ctx, ty)?;
            }
        }
        Ok(())
    }
}

impl Display for Args {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Args::Sub(args) => write!(f, "({})", args.iter().map(ToString::to_string).join(",")),
            Args::Label(l) => l.fmt(f),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Meta => f.write_str("_"),
            Type::Base => f.write_str("*"),
            Type::Arr(s, a, t) => match a {
                Some(a) => write!(f, "{a} | {s} -> {t}"),
                None => write!(f, "{s} -> {t}"),
            },
        }
    }
}

impl Display for Ctx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ctx::Tree(t) => {
                t.fmt(f)?;
            }
            Ctx::Other(xs) => {
                for (name, ty) in xs {
                    match ty {
                        Some(typ) => write!(f, "({name} : {typ})")?,
                        None => name.fmt(f)?,
                    };
                }
            }
        }
        Ok(())
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
