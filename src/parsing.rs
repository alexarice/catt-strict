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

pub(crate) fn comment_one() -> impl Parser<char, (), Error = Simple<char>> + Clone {
    whitespace()
        .separated_by(just("//").ignore_then(newline().not().repeated()))
        .at_least(1)
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
                tr.delimited_by(just("{"), just("}"))
                    .then(el.clone().or_not().padded_by(comment()).map(NoDispOption))
                    .repeated()
                    .at_least(1),
            )
            .foldl(|mut tree, (br, el)| {
                tree.elements.push(el);
                tree.branches.push(br);
                tree
            })
            .or(el
                .padded_by(comment())
                .map(|el| Tree::singleton(NoDispOption(Some(el)))))
    })
}

fn tree_max<O: 'static, P>(
    el: P,
) -> impl Parser<char, Tree<NoDispOption<O>>, Error = Simple<char>> + Clone
where
    P: Parser<char, O, Error = Simple<char>> + Clone + 'static,
{
    recursive(move |tr| {
        tr.padded_by(comment())
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
            })
    })
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
                .or(tree_max(ident()))
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

fn args_with_type<P>(
    term: P,
) -> impl Parser<char, ArgsWithTypeR<Range<usize>>, Error = Simple<char>> + Clone
where
    P: Parser<char, TermRS<Range<usize>>, Error = Simple<char>> + Clone + 'static,
{
    ty_internal(term.clone())
        .map(Box::new)
        .padded_by(comment())
        .then_ignore(just(","))
        .or_not()
        .then(
            term.clone()
                .padded_by(comment())
                .separated_by(just(","))
                .at_least(1),
        )
        .delimited_by(just("("), just(")"))
        .map_with_span(|(ty, tms), sp| ArgsWithTypeR {
            args: ArgsR::Sub(tms),
            ty,
            sp,
        })
        .or(tree(term.clone())
            .then(
                just(":")
                    .ignore_then(ty_internal(term.clone()).padded_by(comment()))
                    .map(Box::new)
                    .or_not(),
            )
            .delimited_by(just("<").or(just("⟨")), just(">").or(just("⟩")))
            .or(tree_max(term.clone()).map(|x| (x, None)))
            .map_with_span(|(l, ty), sp| ArgsWithTypeR {
                args: ArgsR::Label(l),
                ty,
                sp,
            }))
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
    tree(ident())
        .or(tree_max(ident()))
        .map(CtxR::Tree)
        .or(ident()
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
