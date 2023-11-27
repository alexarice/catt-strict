use std::{
    ffi::OsString,
    fmt::{Debug, Display},
    hash::Hash,
    ops::Range,
    path::PathBuf,
};

use ariadne::{Color, Fmt, Report, ReportKind};
use chumsky::{
    prelude::*,
    primitive::just,
    text::{self, TextParser},
    Parser,
};
use pretty::RcDoc;
use thiserror::Error;

use crate::{
    common::{Name, ToDoc},
    eval::SemCtx,
    syntax::{ctx, ident, term, ty, Ctx, Term, Type},
    typecheck::{Environment, TypeCheckError},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Src {
    File(PathBuf),
    Import(String),
    Repl(String),
}

impl Display for Src {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Src::File(p) => f.write_fmt(format_args!("{}", p.display())),
            Src::Import(_) => f.write_str("top_level"),
            Src::Repl(_) => f.write_str("repl"),
        }
    }
}

#[derive(Error, Debug)]
pub enum CattError<Id>
where
    (Id, Range<usize>): ariadne::Span,
{
    #[error(transparent)]
    TypeCheckError(#[from] TypeCheckError<Range<usize>>),
    #[error("Cannot find file: \"{}\"", .0.to_string_lossy().to_string())]
    FileError(PathBuf, Range<usize>),
    #[error("Other report")]
    Report(Vec<Report<'static, (Id, Range<usize>)>>),
}

impl<Id: Debug + Hash + PartialEq + Eq + Clone> CattError<Id> {
    pub fn to_report(self, src: &Id) -> Vec<Report<'static, (Id, Range<usize>)>> {
        let message = self.to_string();
        match self {
            CattError::TypeCheckError(e) => vec![e.to_report(src)],
            CattError::FileError(_, sp) => {
                let report = Report::build(ReportKind::Error, src.clone(), sp.start())
                    .with_message(message)
                    .with_label(
                        ariadne::Label::new((src.clone(), sp))
                            .with_message("Unknown file")
                            .with_color(Color::Red),
                    )
                    .finish();
                vec![report]
            }
            CattError::Report(x) => x,
        }
    }
}

pub enum Command {
    DefHead(Name, Term<Range<usize>>),
    DefCtx(Name, Ctx<Range<usize>>, Term<Range<usize>>),
    DefWT(
        Name,
        Ctx<Range<usize>>,
        Type<Range<usize>>,
        Term<Range<usize>>,
    ),
    Normalise(Ctx<Range<usize>>, Term<Range<usize>>),
    Import(PathBuf, Range<usize>),
}

pub fn command() -> impl Parser<char, Command, Error = Simple<char>> {
    just("def ")
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
            None => Command::DefHead(id, tm),
            Some((ctx, None)) => Command::DefCtx(id, ctx, tm),
            Some((ctx, Some(ty))) => Command::DefWT(id, ctx, ty, tm),
        })
        .or(just("normalise ")
            .ignore_then(ctx())
            .then(just("|").padded().ignore_then(term()))
            .map(|(ctx, tm)| Command::Normalise(ctx, tm)))
        .or(just("import ").ignore_then(
            text::whitespace()
                .at_least(1)
                .not()
                .repeated()
                .at_least(1)
                .collect()
                .map_with_span(|s: String, sp| {
                    let mut pb = PathBuf::from(OsString::from(s));
                    pb.set_extension("catt");
                    Command::Import(pb, sp)
                }),
        ))
}

impl Command {
    pub fn run(self, env: &mut Environment) -> Result<(), CattError<Src>> {
        println!("----------------------------------------");
        match self {
            Command::DefHead(nm, h) => {
                println!("{} {nm}", "Inferring".fg(Color::Green));
                let (ctxt, tmt, tyt) = h.infer(env)?;
                println!(
                    "{}",
                    tmt.to_expr(Some(&ctxt), env.implicits).to_doc().pretty(80)
                );
                println!(
                    "{} {}",
                    "has type".fg(Color::Blue),
                    tyt.to_expr(Some(&ctxt), env.implicits)
                        .to_doc()
                        .nest(9)
                        .pretty(80)
                );
                env.top_level.insert(nm, (ctxt, tmt, tyt));
            }
            Command::DefCtx(nm, ctx, tm) => {
                println!("{} {nm}", "Checking".fg(Color::Green));
                let local = ctx.check(env)?;
                let (tmt, tyt) = tm.check(env, &local)?;
                println!(
                    "{}",
                    tmt.to_expr(Some(&local.ctx), env.implicits)
                        .to_doc()
                        .pretty(80)
                );
                println!(
                    "{} {}",
                    "has type".fg(Color::Blue),
                    tyt.to_expr(Some(&local.ctx), env.implicits)
                        .to_doc()
                        .nest(9)
                        .pretty(80)
                );

                env.top_level.insert(nm, (local.ctx, tmt, tyt));
            }
            Command::DefWT(nm, ctx, ty, tm) => {
                println!(
                    "{} {nm}\n{} {}",
                    "Checking".fg(Color::Green),
                    "has type".fg(Color::Blue),
                    ty.to_doc().nest(9).pretty(80)
                );
                let local = ctx.check(env)?;
                let (tmt, tyt) = tm.check(env, &local)?;
                ty.check(
                    env,
                    &local,
                    &tyt.eval(&SemCtx::id(local.ctx.positions()), env),
                )?;
                println!(
                    "{} {}",
                    "Checked".fg(Color::Blue),
                    tmt.to_expr(Some(&local.ctx), env.implicits)
                        .to_doc()
                        .nest(8)
                        .pretty(80)
                );
                env.top_level.insert(nm, (local.ctx, tmt, tyt));
            }
            Command::Normalise(ctx, tm) => {
                println!("{} {tm}", "Normalising".fg(Color::Green));
                let local = ctx.check(env)?;
                let (tmt, tyt) = tm.check(env, &local)?;
                let sem_ctx = SemCtx::id(local.ctx.positions());
                let tmn = tmt.eval(&sem_ctx, env);
                let tyn = tyt.eval(&sem_ctx, env);
                println!(
                    "{}",
                    RcDoc::group(
                        RcDoc::text("Normal form:".fg(Color::Blue).to_string())
                            .append(
                                RcDoc::line()
                                    .append(
                                        tmn.quote()
                                            .to_expr(Some(&local.ctx), env.implicits)
                                            .to_doc()
                                    )
                                    .nest(2)
                            )
                            .append(RcDoc::line())
                            .append(RcDoc::group(
                                RcDoc::text("has type:".fg(Color::Blue).to_string()).append(
                                    RcDoc::line()
                                        .append(
                                            tyn.quote()
                                                .to_expr(Some(&local.ctx), env.implicits)
                                                .to_doc()
                                        )
                                        .nest(2)
                                )
                            ))
                    )
                    .pretty(80)
                );
            }
            Command::Import(filename, sp) => {
                println!("{} {}", "Importing".fg(Color::Green), filename.display());
                let src = std::fs::read_to_string(&filename)
                    .map_err(|_| CattError::FileError(filename.clone(), sp))?;

                let parsed = command()
                    .separated_by(text::newline().repeated())
                    .then_ignore(end())
                    .parse(src.trim())
                    .map_err(|err| {
                        CattError::Report(
                            err.into_iter()
                                .map(|e| {
                                    Report::build(
                                        ReportKind::Error,
                                        Src::File(filename.clone()),
                                        e.span().start,
                                    )
                                    .with_message(e.to_string())
                                    .with_label(
                                        ariadne::Label::new((
                                            Src::File(filename.clone()),
                                            e.span(),
                                        ))
                                        .with_message(format!("{:?}", e.reason()))
                                        .with_color(Color::Red),
                                    )
                                    .finish()
                                })
                                .collect(),
                        )
                    })?;

                for cmd in parsed {
                    match cmd.run(env) {
                        Ok(_) => {}
                        Err(e) => {
                            return Err(CattError::Report(e.to_report(&Src::File(filename))));
                        }
                    }
                }
                println!("----------------------------------------");
                println!(
                    "{} {}",
                    "Finished importing".fg(Color::Green),
                    filename.display()
                );
            }
        }
        Ok(())
    }
}
