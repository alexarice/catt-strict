use chumsky::{prelude::Simple, primitive::just, text::TextParser, Parser};

use crate::{
    common::Name,
    eval::SemCtx,
    syntax::{ctx, head, ident, term, ty, Ctx, Head, Term, Type},
    typecheck::{Environment, TypeCheckError},
};

pub enum Command {
    LetHead(Name, Head),
    LetCtx(Name, Ctx, Term),
    LetWT(Name, Ctx, Type, Term),
}

pub fn command() -> impl Parser<char, Command, Error = Simple<char>> {
    just("let ")
        .ignore_then(
            ident()
                .padded()
                .then(ctx().or_not())
                .then(just(":").padded().ignore_then(ty()).or_not())
                .then_ignore(just("=").padded()),
        )
        .try_map(|((id, ctx), ty), span| {
            if ty.is_some() && ctx.is_none() {
                Err(Simple::custom(span, "Cannot give type without context"))
            } else {
                Ok((id, ctx, ty))
            }
        })
        .then_with(|(id, ctx, ty)| match (ctx, ty) {
            (None, None) => head().map(move |h| Command::LetHead(id.clone(), h)).boxed(),
            (None, Some(_)) => unreachable!(),
            (Some(ctx), None) => just("")
                .to(ctx)
                .then(term())
                .map(move |(ctx, tm)| Command::LetCtx(id.clone(), ctx, tm))
                .boxed(),
            (Some(ctx), Some(ty)) => just("")
                .to((ctx, ty))
                .then(term())
                .map(move |((ctx, ty), tm)| Command::LetWT(id.clone(), ctx, ty, tm))
                .boxed(),
        })
}

impl Command {
    pub fn run(self, env: &mut Environment) -> Result<(), TypeCheckError> {
        match self {
            Command::LetHead(nm, h) => {
                let x = h.infer(env)?;
                env.top_level.insert(nm, x);
            }
            Command::LetCtx(nm, ctx, tm) => {
                let (ctxt, local) = ctx.check(env)?;
                let (tmt, tyt) = tm.infer(env, &local)?;
                println!("{:?}", tmt.eval(&SemCtx::from_map(&local), env));
                env.top_level.insert(nm, (ctxt, tmt, tyt));
            }
            Command::LetWT(nm, ctx, ty, tm) => {
                let (ctxt, local) = ctx.check(env)?;
                let (tmt, tyt) = tm.infer(env, &local)?;
                ty.check(env, &local, &tyt.eval(&SemCtx::from_map(&local), env))?;
                env.top_level.insert(nm, (ctxt, tmt, tyt));
            }
        }
        Ok(())
    }
}
