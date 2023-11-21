use std::ops::Range;

use chumsky::{prelude::Simple, primitive::just, text::TextParser, Parser};

use crate::{
    common::Name,
    eval::SemCtx,
    syntax::{ctx, ident, term, ty, Ctx, Term, ToDoc, Type},
    typecheck::{Environment, TypeCheckError},
};

pub enum Command {
    LetHead(Name, Term<Range<usize>>),
    LetCtx(Name, Ctx<Range<usize>>, Term<Range<usize>>),
    LetWT(
        Name,
        Ctx<Range<usize>>,
        Type<Range<usize>>,
        Term<Range<usize>>,
    ),
    Normalise(Ctx<Range<usize>>, Term<Range<usize>>),
}

pub fn command() -> impl Parser<char, Command, Error = Simple<char>> {
    just("let ")
        .ignore_then(
            ident()
                .padded()
                .then(
                    ctx()
                        .then(just(":").padded().ignore_then(ty()).or_not())
                        .or_not(),
                )
                .then(just("=").padded().ignore_then(term())),
        )
        .map(|((id, x), tm)| match x {
            None => Command::LetHead(id, tm),
            Some((ctx, None)) => Command::LetCtx(id, ctx, tm),
            Some((ctx, Some(ty))) => Command::LetWT(id, ctx, ty, tm),
        })
        .or(just("normalise ")
            .ignore_then(ctx())
            .then(just("|").padded().ignore_then(term()))
            .map(|(ctx, tm)| Command::Normalise(ctx, tm)))
}

impl Command {
    pub fn run(self, env: &mut Environment) -> Result<(), TypeCheckError<Range<usize>>> {
        println!("----------------------------------------");
        match self {
            Command::LetHead(nm, h) => {
                println!("Inferring {nm}");
                let x = h.infer(env)?;
                println!("{}", x.1.to_expr(Some(&x.0), false).to_doc().pretty(80));
                println!(
                    "  has type {}",
                    x.2.to_expr(Some(&x.0), false).to_doc().nest(11).pretty(80)
                );
                env.top_level.insert(nm, x);
            }
            Command::LetCtx(nm, ctx, tm) => {
                println!("Checking {nm}");
                let local = ctx.check(env)?;
                let (tmt, tyt) = tm.check(env, &local)?;
                println!(
                    "{}",
                    tmt.to_expr(Some(&local.ctx), false).to_doc().pretty(80)
                );
                println!(
                    "  has type {}",
                    tyt.to_expr(Some(&local.ctx), false)
                        .to_doc()
                        .nest(11)
                        .pretty(80)
                );

                env.top_level.insert(nm, (local.ctx, tmt, tyt));
            }
            Command::LetWT(nm, ctx, ty, tm) => {
                println!("Checking {nm} has type {ty}");
                let local = ctx.check(env)?;
                let (tmt, tyt) = tm.check(env, &local)?;
                ty.check(
                    env,
                    &local,
                    &tyt.eval(&SemCtx::id(local.ctx.positions()), env),
                )?;
                println!(
                    "Checked {}",
                    tmt.to_expr(Some(&local.ctx), false).to_doc().pretty(80)
                );
                env.top_level.insert(nm, (local.ctx, tmt, tyt));
            }
            Command::Normalise(ctx, tm) => {
                println!("Normalising {tm}");
                let local = ctx.check(env)?;
                let (tmt, _) = tm.check(env, &local)?;
                let tmn = tmt.eval(&SemCtx::id(local.ctx.positions()), env);
                let quoted = tmn.quote();
                println!(
                    "NF: {}",
                    quoted
                        .to_expr(Some(&local.ctx), false)
                        .to_doc()
                        .nest(4)
                        .pretty(80)
                );
            }
        }
        Ok(())
    }
}
