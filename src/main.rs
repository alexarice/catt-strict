use std::collections::HashMap;

use ariadne::{Color, Label, Report, ReportKind, Source};
use catt_strict::{
    command::command,
    typecheck::{Environment, Reduction, Support},
};
use chumsky::prelude::*;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let src = std::fs::read_to_string(&filename).unwrap();

    let parsed = command()
        .separated_by(text::newline().repeated())
        .then_ignore(end())
        .parse(src.trim());

    match parsed {
        Ok(cmds) => {
            let mut env = Environment {
                top_level: HashMap::new(),
                reduction: Reduction { disc_rem: true },
                support: Support::FullInverse,
            };

            for cmd in cmds {
                match cmd.run(&mut env) {
                    Ok(()) => {}
                    Err(err) => {
                        println!("{err:?}");
                        break;
                    }
                }
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
