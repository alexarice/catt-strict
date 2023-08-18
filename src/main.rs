use ariadne::{Color, ReportKind, Report, Label, Source};
use catt_strict::syntax::term;
use chumsky::prelude::*;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let src = std::fs::read_to_string(&filename).unwrap();

    let parsed = term().then_ignore(end()).parse(src.trim());

    match parsed {
        Ok(t) => println!("Parsed: {t}"),
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
