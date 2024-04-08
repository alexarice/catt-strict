use std::ops::Range;

use chumsky::{
    prelude::*,
    text::{newline, whitespace},
};

use crate::{
    common::{Name, NoDispOption, Spanned, Tree},
    syntax::raw::{ArgsR, ArgsWithTypeR, CtxR, TermR, TermRS, TypeR, TypeRS},
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

fn atom<P>(term: P) -> impl Parser<char, TermRS<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, TermRS<Range<usize>>, Error = Simple<char>> + Clone + 'static,
{
    text::keyword("coh")
        .ignore_then(text::whitespace())
        .ignore_then(
            tree(ident())
                .padded_by(comment())
                .then(just(":").ignore_then(ty_internal(term.clone()).padded_by(comment())))
                .delimited_by(just("["), just("]")),
        )
        .map(|(ctx, ty)| TermR::Coh(ctx, Box::new(ty)))
        .or(text::keyword("comp").to(TermR::Comp))
        .or(text::keyword("id").to(TermR::Id))
        .or(just("_").to(TermR::Hole))
        .or(ident().map(TermR::Var))
        .or(just("S")
            .or(just("Σ"))
            .ignore_then(term.padded_by(comment()).delimited_by(just("("), just(")")))
            .map(|t| TermR::Susp(Box::new(t))))
        .map_with_span(Spanned)
}

fn args<P>(term: P) -> impl Parser<char, ArgsR<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, TermRS<Range<usize>>, Error = Simple<char>> + Clone + 'static,
{
    term.clone()
        .padded_by(comment())
        .separated_by(just(","))
        .at_least(1)
        .delimited_by(just("("), just(")"))
        .map_with_span(Spanned)
        .map(ArgsR::Sub)
        .or(tree(term).map_with_span(Spanned).map(ArgsR::Label))
}

fn args_with_type<P>(
    term: P,
) -> impl Parser<char, ArgsWithTypeR<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, TermRS<Range<usize>>, Error = Simple<char>> + Clone + 'static,
{
    args(term.clone())
        .then(
            ty_internal(term)
                .map(Box::new)
                .padded_by(comment())
                .delimited_by(just("<"), just(">"))
                .or_not(),
        )
        .map(|(args, ty)| ArgsWithTypeR { args, ty })
}

fn ty_internal<P>(term: P) -> impl Parser<char, TypeRS<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, TermRS<Range<usize>>, Error = Simple<char>> + Clone,
{
    let arr = term.clone().then(
        just("->")
            .or(just("→"))
            .padded_by(comment())
            .ignore_then(term.clone()),
    );

    just("*")
        .to(TypeR::Base)
        .or(just("_").to(TypeR::Hole))
        .or(arr.clone().map(|(s, t)| TypeR::Arr(s, None, t)))
        .map_with_span(Spanned)
        .then(
            just("|")
                .padded_by(comment())
                .ignore_then(arr)
                .map_with_span(|x, sp| (x, sp))
                .repeated(),
        )
        .foldl(|a, ((s, t), sp)| {
            let start = a.1.start;
            Spanned(TypeR::Arr(s, Some(Box::new(a)), t), start..sp.end)
        })
}

fn ctx_internal<P>(term: P) -> impl Parser<char, CtxR<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, TermRS<Range<usize>>, Error = Simple<char>> + Clone,
{
    tree(ident()).map(CtxR::Tree).or(ident()
        .padded_by(comment())
        .then(just(":").ignore_then(ty_internal(term.clone()).padded_by(comment())))
        .delimited_by(just("("), just(")"))
        .padded_by(comment())
        .repeated()
        .at_least(1)
        .map(CtxR::Other))
}

pub(crate) fn term() -> impl Parser<char, TermRS<Range<usize>>, Error = Simple<char>> + Clone {
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
            .foldl(|(t, start), (a, end)| (Spanned(TermR::App(Box::new(t), a), start..end), start))
            .map(|(t, _)| t)
    })
}

pub(crate) fn ty() -> impl Parser<char, TypeRS<Range<usize>>, Error = Simple<char>> {
    ty_internal(term())
}

pub(crate) fn ctx() -> impl Parser<char, CtxR<Range<usize>>, Error = Simple<char>> {
    ctx_internal(term())
}
