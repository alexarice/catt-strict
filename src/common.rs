use std::fmt::Display;

use derivative::Derivative;

use crate::term::{TermT, TypeT};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name(pub String);

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Derivative)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tree<T> {
    pub elements: Vec<T>,
    pub branches: Vec<Tree<T>>,
}

impl<T> Tree<T> {
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
        iter: &mut impl Iterator<Item = &'a S>,
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

    pub fn map<U, S>(&self, f: &U) -> Tree<S>
    where
        U: Fn(&T) -> S,
    {
        let branches = self.branches.iter().map(|br| br.map(f)).collect();
        let elements = self.elements.iter().map(f).collect();
        Tree { branches, elements }
    }

    pub fn from_paths<I, S>(&self, iter: &mut I) -> Tree<S>
    where
        I: Iterator<Item = S>,
    {
        let elements = iter.by_ref().take(self.elements.len()).collect();
        let branches = self.branches.iter().map(|br| br.from_paths(iter)).collect();
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
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Path(pub Vec<usize>);

impl Path {
    pub fn susp(mut self, n: usize) -> Self {
        self.0.extend((0..).take(n));
        self
    }

    pub fn de_susp(mut self) -> Self {
        self.0.pop();
        self
    }

    pub fn here(n: usize) -> Self {
        Path(vec![n])
    }

    pub fn extend(mut self, n: usize) -> Path {
        self.0.push(n);
        self
    }

    pub fn to_type(&self) -> TypeT {
        let mut ty = TypeT::Base;
        let mut current_path = Path(vec![]);

        for x in &self.0[0..self.0.len() - 1] {
            let snd = current_path.clone().extend(x + 1);
            current_path = current_path.extend(*x);

            ty = TypeT::Arr(
                TermT::Var(Pos::Path(current_path.clone())),
                Box::new(ty),
                TermT::Var(Pos::Path(snd)),
            )
        }
        ty
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Pos {
    Level(usize),
    Path(Path),
}

impl Pos {
    pub fn susp(self, n: usize) -> Self {
        match self {
            Pos::Level(l) => Pos::Level(l + 2 * n),
            Pos::Path(p) => Pos::Path(p.susp(n)),
        }
    }

    pub fn de_susp(self) -> Self {
        match self {
            Pos::Level(l) => Pos::Level(l - 2),
            Pos::Path(p) => Pos::Path(p.de_susp()),
        }
    }
}