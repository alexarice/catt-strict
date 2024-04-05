use std::ops::Range;

use chumsky::{
    prelude::*,
    text::{newline, whitespace},
};

use crate::{
    common::{Name, NoDispOption, Spanned, Tree},
    syntax::{ArgsE, ArgsWithTypeE, CtxE, TermE, TypeE},
};

pub(crate) fn comment() -> impl Parser<char, (), Error = Simple<char>> + Clone {
    whitespace()
        .separated_by(just("//").ignore_then(newline().not().repeated()))
        .to(())
}

fn tree<O: 'static, P>(
    el: P,
) -> impl Parser<char, Tree<NoDispOption<O>>, Error = Simple<char>> + Clone
where
    P: Parser<char, O, Error = Simple<char>> + Clone + 'static,
{
    recursive(|tr| {
        el.clone()
            .or_not()
            .padded_by(comment())
            .map(NoDispOption)
            .map(Tree::singleton)
            .then(
                tr.then(el.clone().or_not().padded_by(comment()).map(NoDispOption))
                    .repeated(),
            )
            .delimited_by(just("{"), just("}"))
            .foldl(|mut tree, (br, el)| {
                tree.elements.push(el);
                tree.branches.push(br);
                tree
            })
    })
    .or(recursive(move |tr| {
        el.clone()
            .padded_by(comment())
            .separated_by(just(","))
            .at_least(1)
            .delimited_by(just("["), just("]"))
            .map(|xs| Tree {
                elements: (0..=xs.len()).map(|_| NoDispOption(None)).collect(),
                branches: xs
                    .into_iter()
                    .map(|e| Tree::singleton(NoDispOption(Some(e))))
                    .collect(),
            })
            .or(tr
                .padded_by(comment())
                .or(el
                    .clone()
                    .padded_by(comment())
                    .map(|e| Tree::singleton(NoDispOption(Some(e)))))
                .separated_by(just(","))
                .at_least(1)
                .delimited_by(just("["), just("]"))
                .map(|trs| Tree {
                    elements: (0..=trs.len()).map(|_| NoDispOption(None)).collect(),
                    branches: trs,
                }))
    }))
}

pub(crate) fn ident() -> impl Parser<char, Name, Error = Simple<char>> + Clone {
    text::ident().try_map(|x, span| {
        if x == "coh" || x == "comp" || x == "id" || x == "def" || x == "_" {
            Err(Simple::custom(
                span,
                format!("Identifier cannot be \"{x}\""),
            ))
        } else {
            Ok(Name(x))
        }
    })
}

fn atom<P>(term: P) -> impl Parser<char, TermE<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, TermE<Range<usize>>, Error = Simple<char>> + Clone + 'static,
{
    text::keyword("coh")
        .ignore_then(text::whitespace())
        .ignore_then(
            tree(ident())
                .padded_by(comment())
                .then(just(":").ignore_then(ty_internal(term.clone()).padded_by(comment())))
                .delimited_by(just("["), just("]")),
        )
        .map_with_span(|(ctx, ty), sp| TermE::Coh(ctx, Box::new(ty), sp))
        .or(text::keyword("comp").map_with_span(|_, s| TermE::Comp(s)))
        .or(text::keyword("id").map_with_span(|_, s| TermE::Id(s)))
        .or(just("_").map_with_span(|_, sp| TermE::Hole(sp)))
        .or(ident().map_with_span(TermE::Var))
        .or(just("S").or(just("Σ"))
            .ignore_then(term.padded_by(comment()).delimited_by(just("("), just(")")))
            .map_with_span(|t, sp| TermE::Susp(Box::new(t), sp)))
}

fn args<P>(term: P) -> impl Parser<char, ArgsE<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, TermE<Range<usize>>, Error = Simple<char>> + Clone + 'static,
{
    term.clone()
        .padded_by(comment())
        .separated_by(just(","))
        .at_least(1)
        .delimited_by(just("("), just(")"))
        .map_with_span(Spanned)
        .map(ArgsE::Sub)
        .or(tree(term).map_with_span(Spanned).map(ArgsE::Label))
}

fn args_with_type<P>(
    term: P,
) -> impl Parser<char, ArgsWithTypeE<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, TermE<Range<usize>>, Error = Simple<char>> + Clone + 'static,
{
    args(term.clone())
        .then(
            ty_internal(term)
                .map(Box::new)
                .padded_by(comment())
                .delimited_by(just("<"), just(">"))
                .or_not(),
        )
        .map(|(args, ty)| ArgsWithTypeE { args, ty })
}

fn ty_internal<P>(term: P) -> impl Parser<char, TypeE<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, TermE<Range<usize>>, Error = Simple<char>> + Clone,
{
    let arr = term
        .clone()
        .then(just("->").or(just("→")).padded_by(comment()).ignore_then(term.clone()));

    just("*")
        .map_with_span(|_, sp| TypeE::Base(sp))
        .or(just("_").map_with_span(|_, sp| TypeE::Hole(sp)))
        .or(arr.map_with_span(|(s, t), sp| TypeE::Arr(s, None, t, sp)))
        .then(
            just("|")
                .padded_by(comment())
                .ignore_then(
                    term.clone()
                        .padded_by(comment())
                        .then(just("->").or(just("→")).ignore_then(term.padded_by(comment()))),
                )
                .map_with_span(|x, sp| (x, sp))
                .repeated(),
        )
        .foldl(|a, ((s, t), sp)| TypeE::Arr(s, Some(Box::new(a)), t, sp))
}

fn ctx_internal<P>(term: P) -> impl Parser<char, CtxE<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, TermE<Range<usize>>, Error = Simple<char>> + Clone,
{
    tree(ident()).map(CtxE::Tree).or(ident()
        .padded_by(comment())
        .then(just(":").ignore_then(ty_internal(term.clone()).padded_by(comment())))
        .delimited_by(just("("), just(")"))
        .padded_by(comment())
        .repeated()
        .at_least(1)
        .map(CtxE::Other))
}

pub(crate) fn term() -> impl Parser<char, TermE<Range<usize>>, Error = Simple<char>> + Clone {
    recursive(|term| {
        atom(term.clone())
            .map_with_span(|t, sp| (t, sp.start()))
            .padded_by(comment())
            .then(
                args_with_type(term.clone())
                    .padded_by(comment())
                    .map_with_span(|a, sp| (a, sp.end()))
                    .repeated()
                    .at_most(1),
            )
            .foldl(|(t, start), (a, end)| (TermE::App(Box::new(t), a, start..end), start))
            .map(|(t, _)| t)
    })
}

pub(crate) fn ty() -> impl Parser<char, TypeE<Range<usize>>, Error = Simple<char>> {
    ty_internal(term())
}

pub(crate) fn ctx() -> impl Parser<char, CtxE<Range<usize>>, Error = Simple<char>> {
    ctx_internal(term())
}
