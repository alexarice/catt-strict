use std::{
    collections::{hash_map::Entry, HashMap},
    fmt, fs,
    path::PathBuf,
};

use ariadne::{Cache, Color, Report, ReportKind, Source};
use catt_strict::{
    command::{command, Command, Src},
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

    /// Start repl
    #[arg(short, long)]
    interactive: bool,

    /// Catt files to import
    #[arg(value_name = "FILE")]
    imports: Vec<PathBuf>,
}

#[derive(Default, Debug, Clone)]
struct MyCache {
    files: HashMap<Src, Source>,
}

impl Cache<Src> for MyCache {
    fn fetch(&mut self, path: &Src) -> Result<&Source, Box<dyn fmt::Debug + '_>> {
        Ok(match self.files.entry(path.clone()) {
            // TODO: Don't allocate here
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(match path {
                Src::File(p) => Source::from(&fs::read_to_string(p).map_err(|e| Box::new(e) as _)?),
                Src::Import(s) => Source::from(s),
                Src::Repl(s) => Source::from(s),
            }),
        })
    }
    fn display<'a>(&self, path: &'a Src) -> Option<Box<dyn fmt::Display + 'a>> {
        Some(Box::new(format!("{}", path)))
    }
}

fn main() {
    let args: Args = clap::Parser::parse();

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

    let mut cache = MyCache::default();

    for path in args.imports {
        let string = path.to_str().unwrap().to_owned();
        match Command::Import(path, 0..string.len()).run(&mut env) {
            Ok(_) => {}
            Err(err) => err
                .to_report(&Src::Import(string))
                .into_iter()
                .for_each(|rep| {
                    rep.print(&mut cache).unwrap();
                }),
        }
    }

    if args.interactive {
        let mut rl = rustyline::DefaultEditor::new().unwrap();
        loop {
            let readline = rl.readline("Catt>> ");

            match readline {
                Ok(s) => {
                    if s == "exit" || s == "quit" {
                        break;
                    } else {
                        match command().then_ignore(end()).parse(s.trim()) {
                            Ok(command) => match command.run(&mut env) {
                                Ok(_) => {}
                                Err(err) => err
                                    .to_report(&Src::Repl(s.clone()))
                                    .into_iter()
                                    .for_each(|rep| {
                                        rep.print(&mut cache).unwrap();
                                    }),
                            },
                            Err(err) => err.into_iter().for_each(|e| {
                                Report::build(
                                    ReportKind::Error,
                                    Src::Repl(s.clone()),
                                    e.span().start,
                                )
                                .with_message(e.to_string())
                                .with_label(
                                    ariadne::Label::new((Src::Repl(s.clone()), e.span()))
                                        .with_message(format!("{:?}", e.reason()))
                                        .with_color(Color::Red),
                                )
                                .finish()
                                .print(&mut cache)
                                .unwrap()
                            }),
                        }
                    }
                }
                Err(_) => break,
            }
        }
    }
}
