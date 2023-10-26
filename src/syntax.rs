use crate::common::{Name, NoDispOption, Tree};
use chumsky::{prelude::*, text::keyword};
use itertools::Itertools;
use std::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Head {
    Susp(Box<Head>),
    TopLvl(Name),
    Coh(Tree<NoDispOption<Name>>, Box<Type>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(Name),
    WithArgs(Head, Args, Option<Box<Type>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Args {
    Sub(Vec<Term>),
    Label(Tree<NoDispOption<Term>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Base,
    Arr(Term, Option<Box<Type>>, Term),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ctx {
    Tree(Tree<NoDispOption<Name>>),
    Other(Vec<(Name, NoDispOption<Type>, bool)>),
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
            tree(ident().padded().or_not().map(NoDispOption))
                .padded()
                .then(just(":").ignore_then(ty(term.clone()).padded()))
                .delimited_by(just("["), just("]"))
                .padded()
                .map(|(ctx, ty)| Term::Coh(ctx, Box::new(ty))),
        )
        .or(ident().map(|x| Term::Var(x)))
        .or(just("_").to(Term::Hole))
        .or(just("‼")
            .ignore_then(term.padded().delimited_by(just("("), just(")")))
            .map(|t| Term::Susp(Box::new(t))))
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
            .map(|i| (i, NoDispOption(None), false))
            .or(ident()
                .padded()
                .delimited_by(just("{"), just("}"))
                .map(|i| (i, NoDispOption(None), true)))
            .or(ident().padded().then(
                just(":")
                    .ignore_then(ty(term.clone()).padded()))
                .delimited_by(just("("), just(")"))
                .map(|(i, ty)| (i, NoDispOption(Some(ty)), false))
            )
	    .or(ident().padded().then(
                just(":")
                    .ignore_then(ty(term).padded()))
                .delimited_by(just("{"), just("}"))
                .map(|(i, ty)| (i, NoDispOption(Some(ty)), true))
            )
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
	    Term::Hole => {
                f.write_str("_")?;
            }
            Term::App(t, a, ty) => {
                t.fmt(f)?;
                a.fmt(f)?;
                if let Some(typ) = ty {
                    write!(f, "<{}>", typ)?;
                }
            }
            Term::Susp(t) => {
                write!(f, "‼({})", t)?;
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
                for (name, ty, icit) in xs {
                    match (&ty.0, icit) {
                        (Some(typ), true) => write!(f, "{{{name} : {typ}}}")?,
			(Some(typ), false) => write!(f, "({name} : {typ})")?,
                        (None, true) => write!(f, "{{{name}}}")?,
			(None, false) => name.fmt(f)?,
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
