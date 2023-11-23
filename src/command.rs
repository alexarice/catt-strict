use std::{ffi::OsString, fmt::Debug, hash::Hash, ops::Range, path::PathBuf};

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
    pub fn run(self, env: &mut Environment) -> Result<(), CattError<Option<PathBuf>>> {
        println!("----------------------------------------");
        match self {
            Command::DefHead(nm, h) => {
                println!("{} {nm}", "Inferring".fg(Color::Green));
                let x = h.infer(env)?;
                println!("{}", x.1.to_expr(Some(&x.0), false).to_doc().pretty(80));
                println!(
                    "{} {}",
                    "has type".fg(Color::Blue),
                    x.2.to_expr(Some(&x.0), false).to_doc().nest(9).pretty(80)
                );
                env.top_level.insert(nm, x);
            }
            Command::DefCtx(nm, ctx, tm) => {
                println!("{} {nm}", "Checking".fg(Color::Green));
                let local = ctx.check(env)?;
                let (tmt, tyt) = tm.check(env, &local)?;
                println!(
                    "{}",
                    tmt.to_expr(Some(&local.ctx), false).to_doc().pretty(80)
                );
                println!(
                    "{} {}",
                    "has type".fg(Color::Blue),
                    tyt.to_expr(Some(&local.ctx), false)
                        .to_doc()
                        .nest(9)
                        .pretty(80)
                );

                env.top_level.insert(nm, (local.ctx, tmt, tyt));
            }
            Command::DefWT(nm, ctx, ty, tm) => {
                println!(
                    "{} {nm} {} {ty}",
                    "Checking".fg(Color::Green),
                    "has type".fg(Color::Blue)
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
                    tmt.to_expr(Some(&local.ctx), false)
                        .to_doc()
                        .nest(8)
                        .pretty(80)
                );
                env.top_level.insert(nm, (local.ctx, tmt, tyt));
            }
            Command::Normalise(ctx, tm) => {
                println!("{} {tm}", "Normalising".fg(Color::Green));
                let local = ctx.check(env)?;
                let (tmt, _) = tm.check(env, &local)?;
                let tmn = tmt.eval(&SemCtx::id(local.ctx.positions()), env);
                let quoted = tmn.quote();
                println!(
                    "{}",
                    RcDoc::group(
                        RcDoc::text("Normal form:".fg(Color::Blue).to_string()).append(
                            RcDoc::line()
                                .append(quoted.to_expr(Some(&local.ctx), false).to_doc())
                                .nest(2)
                        )
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
                                        filename.clone(),
                                        e.span().start,
                                    )
                                    .with_message(e.to_string())
                                    .with_label(
                                        ariadne::Label::new((Some(filename.clone()), e.span()))
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
                            return Err(CattError::Report(e.to_report(&Some(filename))));
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
