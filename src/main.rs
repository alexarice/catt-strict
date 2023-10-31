use std::collections::HashMap;

use ariadne::{Color, Label, Report, ReportKind, Source};
use catt_strict::{
    syntax::{ctx, term},
    typecheck::Environment,
};
use chumsky::prelude::*;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let src = std::fs::read_to_string(&filename).unwrap();

    let parsed = ctx(term())
        .padded()
        .then(term().then_ignore(end()))
        .parse(src.trim());

    match parsed {
        Ok((ctx, tm)) => {
            println!("Parsed: {ctx} {tm}");

	    let env = Environment {
                top_level: HashMap::new(),
                local: HashMap::new(),
            };

	    match ctx.to_env(&env).and_then(|(ctxt, local)| {
		println!("Ctx: {ctxt:?}");
		let new_env = Environment {
		    top_level: HashMap::new(),
		    local,
		};
		let x = tm.infer(&new_env)?;
		Ok((new_env, x))
	    }) {
		Ok((new_env, (tmt, tyt))) => {
		    println!("Term {tmt:#?}");
		    println!("Type {tyt:#?}");

		    println!("Norm: {:#?}", tmt.eval(&new_env.get_sem_ctx()).quote())
		},
		Err(err) => {
		    println!("Error: {err:#?}");
		},
	    }
        }
        Err(errs) => errs.into_iter().for_each(|e| {
            Report::build(ReportKind::Error, &filename, e.span().start)
                .with_message(e.to_string())
                .with_label(
                    Label::new((&filename, e.span()))
                        .with_message(format!("{:?}", e.reason()))
                        .with_color(Color::Red),
                )
                .finish()
                .print((&filename, Source::from(&src)))
                .unwrap()
        }),
    }
}
