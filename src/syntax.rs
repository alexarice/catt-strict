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
pub struct ArgsWithType {
    pub args: Args,
    pub ty: Option<Box<Type>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(Name),
    WithArgs(Head, ArgsWithType),
    App(Box<Term>, ArgsWithType),
}

pub type Sub = Vec<Term>;
pub type Label = Tree<NoDispOption<Term>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Args {
    Sub(Sub),
    Label(Label),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Base,
    Arr(Term, Option<Box<Type>>, Term),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ctx {
    Tree(Tree<NoDispOption<Name>>),
    Other(Vec<(Name, Type)>),
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

fn head_internal<P>(term: P) -> impl Parser<char, Head, Error = Simple<char>> + Clone
where
    P: Parser<char, Term, Error = Simple<char>> + Clone + 'static,
{
    recursive(|head| {
        keyword("coh")
            .ignore_then(
                tree(ident().padded().or_not().map(NoDispOption))
                    .padded()
                    .then(just(":").ignore_then(ty_internal(term.clone()).padded()))
                    .delimited_by(just("["), just("]"))
                    .padded()
                    .map(|(ctx, ty)| Head::Coh(ctx, Box::new(ty))),
            )
            .or(ident().map(|x| Head::TopLvl(x)))
            .or(just("‼")
                .ignore_then(head.padded())
                .map(|t| Head::Susp(Box::new(t))))
    })
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

fn args_with_type<P>(term: P) -> impl Parser<char, ArgsWithType, Error = Simple<char>> + Clone
where
    P: Parser<char, Term, Error = Simple<char>> + Clone + 'static,
{
    args(term.clone())
        .then(
            ty_internal(term)
                .map(|ty| Box::new(ty))
                .padded()
                .delimited_by(just("<"), just(">"))
                .or_not(),
        )
        .map(|(args, ty)| ArgsWithType { args, ty })
}

fn ty_internal<P>(term: P) -> impl Parser<char, Type, Error = Simple<char>> + Clone
where
    P: Parser<char, Term, Error = Simple<char>> + Clone,
{
    let arr = term
        .clone()
        .then(just("->").padded().ignore_then(term.clone()));

    just("*")
        .to(Type::Base)
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

fn ctx_internal<P>(term: P) -> impl Parser<char, Ctx, Error = Simple<char>> + Clone
where
    P: Parser<char, Term, Error = Simple<char>> + Clone,
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

pub fn term() -> impl Parser<char, Term, Error = Simple<char>> + Clone {
    recursive(|term| {
        head_internal(term.clone())
            .padded()
            .then(args_with_type(term.clone()).padded().repeated().at_least(1))
            .map(|(head, mut args)| {
                let fst_arg = args.remove(0);
                (Term::WithArgs(head, fst_arg), args)
            })
            .foldl(|t, a| Term::App(Box::new(t), a))
            .or(ident().map(|x| Term::Var(x)))
    })
}

pub fn ty() -> impl Parser<char, Type, Error = Simple<char>> {
    ty_internal(term())
}

pub fn head() -> impl Parser<char, Head, Error = Simple<char>> {
    head_internal(term())
}

pub fn ctx() -> impl Parser<char, Ctx, Error = Simple<char>> {
    ctx_internal(term())
}

impl Display for Head {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Head::Susp(head) => {
                write!(f, "‼ {}", head)?;
            }
            Head::TopLvl(x) => {
                x.fmt(f)?;
            }
            Head::Coh(ctx, ty) => {
                write!(f, "coh [{} : {}]", ctx, ty)?;
            }
        }
        Ok(())
    }
}

impl Display for ArgsWithType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.args.fmt(f)?;
        if let Some(typ) = &self.ty {
            write!(f, "<{}>", typ)?;
        }
        Ok(())
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::App(t, a) => {
                t.fmt(f)?;
                a.fmt(f)?;
            }
            Term::Var(name) => {
                name.0.fmt(f)?;
            }
            Term::WithArgs(head, args) => {
                head.fmt(f)?;
                args.fmt(f)?;
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
                    write!(f, "({name} : {ty})")?;
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
