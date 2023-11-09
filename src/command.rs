use chumsky::{prelude::Simple, primitive::just, text::TextParser, Parser};

use crate::{
    common::Name,
    eval::SemCtx,
    syntax::{ctx, ident, term, ty, Ctx, Term, Type},
    typecheck::{Environment, TypeCheckError},
};

pub enum Command {
    LetHead(Name, Term),
    LetCtx(Name, Ctx, Term),
    LetWT(Name, Ctx, Type, Term),
    Normalise(Ctx, Term),
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
            (None, None) => term().map(move |h| Command::LetHead(id.clone(), h)).boxed(),
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
        .or(just("normalise ")
            .ignore_then(ctx())
            .then(just("|").padded().ignore_then(term()))
            .map(|(ctx, tm)| Command::Normalise(ctx, tm)))
}

impl Command {
    pub fn run(self, env: &mut Environment) -> Result<(), TypeCheckError> {
        println!("----------------------------------------");
        match self {
            Command::LetHead(nm, h) => {
                println!("Inferring {nm}");
                let x = h.infer(env)?;
                println!("{}", x.1.to_expr(Some(&x.0), false));
                println!("  has type {}", x.2.to_expr(Some(&x.0), false));
                env.top_level.insert(nm, x);
            }
            Command::LetCtx(nm, ctx, tm) => {
                println!("Checking {nm}");
                let (ctxt, local) = ctx.check(env)?;
                let (tmt, tyt) = tm.check(env, &local)?;
                println!("{}", tmt.to_expr(Some(&ctxt), false));
                println!("  has type {}", tyt.to_expr(Some(&ctxt), false));

                env.top_level.insert(nm, (ctxt, tmt, tyt));
            }
            Command::LetWT(nm, ctx, ty, tm) => {
                println!("Checking {nm} has type {ty}");
                let (ctxt, local) = ctx.check(env)?;
                let (tmt, tyt) = tm.check(env, &local)?;
                ty.check(env, &local, &tyt.eval(&SemCtx::id(), env))?;
                println!("Checked {}", tmt.to_expr(Some(&ctxt), false));
                env.top_level.insert(nm, (ctxt, tmt, tyt));
            }
            Command::Normalise(ctx, tm) => {
                println!("Normalising {tm}");
                let (ctxt, local) = ctx.check(env)?;
                let (tmt, _) = tm.check(env, &local)?;
                let tmn = tmt.eval(&SemCtx::id(), env);
                let quoted = tmn.quote();
                println!("NF: {}", quoted.to_expr(Some(&ctxt), false));
            }
        }
        Ok(())
    }
}
