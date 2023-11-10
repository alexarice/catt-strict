use std::fmt::Display;

use derivative::Derivative;
use itertools::Itertools;

use crate::term::{TermT, TypeT};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name(pub String);

impl<'a> From<&'a str> for Name {
    fn from(value: &'a str) -> Self {
        Name(value.to_string())
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Debug, Derivative)]
#[derivative(Default(bound = ""))]
pub struct NoDispOption<T>(pub Option<T>);

impl<T: Display> Display for NoDispOption<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            Some(e) => e.fmt(f),
            None => Ok(()),
        }
    }
}

impl<T> PartialEq for NoDispOption<T> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl<T> Eq for NoDispOption<T> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tree<T> {
    pub elements: Vec<T>,
    pub branches: Vec<Tree<T>>,
}

impl<T> Tree<T> {
    pub fn is_disc(&self) -> bool {
        self.branches.is_empty() || (self.branches.len() == 1 && self.branches[0].is_disc())
    }

    pub fn dim(&self) -> usize {
        self.branches
            .iter()
            .map(|br| br.dim())
            .max()
            .map(|x| x + 1)
            .unwrap_or_default()
    }

    pub fn susp_level(&self) -> usize {
        if self.branches.len() == 1 {
            1 + self.branches[0].susp_level()
        } else {
            0
        }
    }

    pub fn get_maximal_elements(&self) -> Vec<&T> {
        if self.branches.is_empty() {
            vec![self.elements.last().unwrap().clone()]
        } else {
            self.branches
                .iter()
                .flat_map(|br| br.get_maximal_elements())
                .collect()
        }
    }

    pub fn get_maximal_paths(&self) -> Vec<Path> {
        if self.branches.is_empty() {
            vec![Path::here(0)]
        } else {
            self.branches
                .iter()
                .enumerate()
                .flat_map(|(i, br)| br.get_maximal_paths().into_iter().map(move |p| p.extend(i)))
                .collect()
        }
    }

    pub fn get_maximal_with_branching(&self) -> Vec<(Path, usize, &T)> {
        if self.branches.is_empty() {
            vec![(Path::here(0), 0, &self.elements[0])]
        } else {
            self.branches
                .iter()
                .enumerate()
                .flat_map(|(i, br)| {
                    let v = br.get_maximal_with_branching();
                    let linear = v.len() == 1;
                    v.into_iter().map(move |(p, bh, el)| {
                        if linear {
                            (Path::here(i), 0, el)
                        } else {
                            (p.extend(i), bh + 1, el)
                        }
                    })
                })
                .collect()
        }
    }

    pub fn get_paths(&self) -> Vec<(Path, &T)> {
        self.elements
            .iter()
            .enumerate()
            .map(|(i, t)| (Path::here(i), t))
            .chain(self.branches.iter().enumerate().flat_map(|(i, br)| {
                br.get_paths()
                    .into_iter()
                    .map(move |(p, t)| (p.extend(i), t))
            }))
            .collect()
    }

    pub fn singleton(i: T) -> Self {
        Tree {
            elements: vec![i],
            branches: vec![],
        }
    }

    pub fn label_from_max<'a, S: Clone + 'a>(
        &self,
        iter: &mut impl Iterator<Item = S>,
    ) -> Option<Tree<NoDispOption<S>>> {
        if self.branches.is_empty() {
            return iter
                .next()
                .map(|i| Tree::singleton(NoDispOption(Some(i.clone()))));
        }
        let branches = self
            .branches
            .iter()
            .map(|tr| tr.label_from_max(iter))
            .collect::<Option<Vec<_>>>()?;

        let elements = self.elements.iter().map(|_| NoDispOption(None)).collect();

        Some(Tree { elements, branches })
    }

    pub fn map_ref<U, S>(&self, f: &U) -> Tree<S>
    where
        U: Fn(&T) -> S,
    {
        let branches = self.branches.iter().map(|br| br.map_ref(f)).collect();
        let elements = self.elements.iter().map(f).collect();
        Tree { branches, elements }
    }

    pub fn map<U, S>(self, f: &U) -> Tree<S>
    where
        U: Fn(T) -> S,
    {
        let branches = self.branches.into_iter().map(|br| br.map(f)).collect();
        let elements = self.elements.into_iter().map(f).collect();
        Tree { branches, elements }
    }

    pub fn path_tree(&self) -> Tree<Path> {
        let elements = (0..self.elements.len()).map(Path::here).collect();
        let branches = self
            .branches
            .iter()
            .enumerate()
            .map(|(i, br)| br.path_tree().map(&|p| p.extend(i)))
            .collect();

        Tree { elements, branches }
    }

    pub fn susp(self) -> Self
    where
        T: Default,
    {
        Tree {
            elements: vec![Default::default(), Default::default()],
            branches: vec![self],
        }
    }

    pub fn lookup(&self, p: &Path) -> Option<&T> {
        let mut tr = self;
        for x in p.path.iter().rev() {
            tr = tr.branches.get(*x)?;
        }
        tr.elements.get(p.here)
    }

    pub fn insertion(&mut self, mut bp: Path, inner: Tree<T>) {
        match bp.path.pop() {
            Some(i) => {
                let (s, t) = inner.elements.into_iter().collect_tuple().unwrap();
                self.elements[i] = s;
                self.elements[i + 1] = t;
                self.branches[i].insertion(bp, inner.branches.into_iter().next().unwrap());
            }
            None => {
                self.elements.splice(bp.here..bp.here + 2, inner.elements);
                self.branches.splice(bp.here..bp.here + 1, inner.branches);
            }
        }
    }

    pub fn unwrap_disc(self) -> T {
        if self.branches.is_empty() {
            self.elements.into_iter().next().unwrap()
        } else {
            self.branches.into_iter().next().unwrap().unwrap_disc()
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Path {
    pub here: usize,
    pub path: Vec<usize>,
}

impl Path {
    pub fn susp(self) -> Self {
        self.extend(0)
    }

    pub fn de_susp(mut self, d: usize) -> Self {
        for _ in 0..d {
            self.path.pop();
        }

        self
    }

    pub fn here(n: usize) -> Self {
        Path {
            here: n,
            path: vec![],
        }
    }

    pub fn extend(mut self, n: usize) -> Path {
        self.path.push(n);
        self
    }

    pub fn to_type(&self) -> TypeT {
        let mut ty = TypeT::Base;
        let mut current_path = vec![];

        for x in self.path.iter().rev() {
            let fst = Path {
                here: *x,
                path: current_path.clone(),
            };

            let snd = Path {
                here: x + 1,
                path: current_path.clone(),
            };

            current_path.push(*x);

            ty = TypeT::Arr(
                TermT::Var(Pos::Path(fst)),
                Box::new(ty),
                TermT::Var(Pos::Path(snd)),
            )
        }
        ty
    }

    pub fn fst_mut(&mut self) -> &mut usize {
        self.path.last_mut().unwrap_or(&mut self.here)
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for x in self.path.iter().rev() {
            write!(f, "{x}")?;
        }
        write!(f, "{}", self.here)?;
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Pos {
    Level(usize),
    Path(Path),
}

impl Pos {
    pub fn susp(self) -> Self {
        match self {
            Pos::Level(l) => Pos::Level(l + 2),
            Pos::Path(p) => Pos::Path(p.susp()),
        }
    }

    pub fn de_susp(self) -> Self {
        match self {
            Pos::Level(l) => Pos::Level(l - 2),
            Pos::Path(p) => Pos::Path(p.de_susp(1)),
        }
    }
}

impl Display for Pos {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pos::Level(l) => write!(f, "l{l}"),
            Pos::Path(p) => write!(f, "p{p}"),
        }
    }
}
