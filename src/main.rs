use std::{
    collections::{hash_map::Entry, HashMap},
    fmt, fs,
    path::PathBuf,
};

use ariadne::{Cache, Source};
use catt_strict::{
    command::Command,
    typecheck::{Environment, Insertion, Reduction, Support},
};

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

#[derive(Default, Debug, Clone)]
pub struct MyCache {
    files: HashMap<Option<PathBuf>, Source>,
}

impl Cache<Option<PathBuf>> for MyCache {
    fn fetch(&mut self, path: &Option<PathBuf>) -> Result<&Source, Box<dyn fmt::Debug + '_>> {
        Ok(match self.files.entry(path.clone()) {
            // TODO: Don't allocate here
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(if let Some(p) = path {
                Source::from(&fs::read_to_string(p).map_err(|e| Box::new(e) as _)?)
            } else {
                Source::from("")
            }),
        })
    }
    fn display<'a>(&self, path: &'a Option<PathBuf>) -> Option<Box<dyn fmt::Display + 'a>> {
        if let Some(p) = path {
            Some(Box::new(p.display()))
        } else {
            Some(Box::new("top_level"))
        }
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

    match Command::Import(args.filename, 0..0).run(&mut env) {
        Ok(_) => {}
        Err(err) => err.to_report(&None).into_iter().for_each(|rep| {
            rep.print(MyCache::default()).unwrap();
        }),
    }
}
