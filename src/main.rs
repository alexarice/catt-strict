use std::{collections::HashMap, path::PathBuf};

use ariadne::{Color, Label, Report, ReportKind, Source};
use catt_strict::{
    command::command,
    typecheck::{Environment, Insertion, Reduction, Support},
};
use chumsky::prelude::*;

#[derive(clap::Parser)]
/// Interpreter for semistrict variations of Catt
struct Args {
    /// Turn on strict unit normalisation
    #[arg(long)]
    su: bool,

    /// Turn on strict unit and associator normalisation (implies units)
    #[arg(long)]
    sua: bool,

    /// Turn off fullness check
    #[arg(long)]
    no_fullness_check: bool,

    /// Catt file to import
    #[arg(value_name = "FILE")]
    filename: PathBuf,
}

fn main() {
    let args: Args = clap::Parser::parse();
    let filename = args.filename;
    let src = std::fs::read_to_string(&filename).unwrap();

    let mut env = Environment {
        top_level: HashMap::new(),
        reduction: Reduction {
            disc_rem: args.su || args.sua,
            endo_coh: args.su || args.sua,
            insertion: if args.sua {
                Some(Insertion::Full)
            } else if args.su {
                Some(Insertion::Pruning)
            } else {
                None
            },
        },
        support: if args.no_fullness_check {
            Support::FullInverse
        } else {
            Support::NoInverse
        },
    };

    let parsed = command()
        .separated_by(text::newline().repeated())
        .then_ignore(end())
        .parse(src.trim());

    let fn_str = filename.to_string_lossy().into_owned();

    match parsed {
        Ok(cmds) => {
            for cmd in cmds {
                match cmd.run(&mut env) {
                    Ok(_) => {}
                    Err(e) => {
                        e.to_report(&fn_str)
                            .print((&fn_str, Source::from(&src)))
                            .unwrap();
                        break;
                    }
                }
            }
        }
        Err(errs) => errs.into_iter().for_each(|e| {
            Report::build(ReportKind::Error, &fn_str, e.span().start)
                .with_message(e.to_string())
                .with_label(
                    Label::new((&fn_str, e.span()))
                        .with_message(format!("{:?}", e.reason()))
                        .with_color(Color::Red),
                )
                .finish()
                .print((&fn_str, Source::from(&src)))
                .unwrap()
        }),
    }
}
