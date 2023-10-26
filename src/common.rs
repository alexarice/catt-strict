use std::fmt::Display;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name(pub String);

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NoDispOption<T>(pub Option<T>);

impl<T: Display> Display for NoDispOption<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            Some(e) => e.fmt(f),
            None => Ok(()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tree<T> {
    pub elements: Vec<T>,
    pub branches: Vec<Tree<T>>,
}

impl<T> Tree<T> {
    pub fn get_paths(&self) -> Vec<(Path, &T)> {
        let mut pairs = vec![];
        self.collect_paths(&Path(vec![]), &mut pairs);
        pairs
    }

    fn collect_paths<'a>(&'a self, current_path: &Path, pairs: &mut Vec<(Path, &'a T)>) {
        for (i, x) in self.elements.iter().enumerate() {
            pairs.push((current_path.clone().extend(i), x));
        }
        let mut path = current_path.clone().extend(0);
        for x in &self.branches {
            x.collect_paths(&path, pairs);
            let len = path.0.len();
            path.0[len] += 1;
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Path(pub Vec<usize>);

impl Path {
    pub fn extend(mut self, n: usize) -> Path {
        self.0.push(n);
        self
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Pos {
    Level(usize),
    Path(Path),
}
