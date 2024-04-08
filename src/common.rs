use std::{collections::HashMap, fmt::Display};

use derivative::Derivative;
use either::Either;
use itertools::Itertools;
use pretty::RcDoc;

use crate::{
    eval::SemCtx,
    syntax::core::{ArgsC, TermC, TypeC},
    syntax::normal::TermN,
    syntax::raw::TermR,
    typecheck::TypeCheckError,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name(pub(crate) String);

impl<'a> From<&'a str> for Name {
    fn from(value: &'a str) -> Self {
        Name(value.to_string())
    }
}

pub trait ToDoc {
    fn to_doc(&self) -> RcDoc<'_>;
}

impl ToDoc for Name {
    fn to_doc(&self) -> pretty::RcDoc<'_> {
        RcDoc::text(&self.0)
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Debug, Derivative)]
#[derivative(Default(bound = ""))]
pub struct NoDispOption<T>(pub(crate) Option<T>);

impl<T: ToDoc> ToDoc for NoDispOption<T> {
    fn to_doc(&self) -> RcDoc<'_> {
        match &self.0 {
            Some(x) => x.to_doc(),
            None => RcDoc::nil(),
        }
    }
}

impl<T: Display> Display for NoDispOption<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            NoDispOption(Some(e)) => e.fmt(f),
            _ => Ok(()),
        }
    }
}

impl<T> PartialEq for NoDispOption<T> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl<T> Eq for NoDispOption<T> {}

#[derive(Clone, Debug)]
pub struct Spanned<T, S>(pub(crate) T, pub(crate) S);

impl<T: ToDoc, S> ToDoc for Spanned<T, S> {
    fn to_doc(&self) -> RcDoc<'_> {
        self.0.to_doc()
    }
}

impl<T: Display, S> Display for Spanned<T, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: PartialEq, S> PartialEq for Spanned<T, S> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<T: Eq, S> Eq for Spanned<T, S> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tree<T> {
    pub(crate) elements: Vec<T>,
    pub(crate) branches: Vec<Tree<T>>,
}

impl<T> Tree<T> {
    pub(crate) fn is_disc(&self) -> bool {
        self.branches.is_empty() || (self.branches.len() == 1 && self.branches[0].is_disc())
    }

    /// Get the unique maximal element if there is one
    pub(crate) fn get_max(&self) -> Option<&T> {
        match self.branches.len() {
            0 => Some(&self.elements[0]),
            1 => self.branches[0].get_max(),
            _ => None,
        }
    }

    pub(crate) fn dim(&self) -> usize {
        self.branches
            .iter()
            .map(|br| br.dim())
            .max()
            .map(|x| x + 1)
            .unwrap_or_default()
    }

    pub(crate) fn bdry_set(&self, n: usize, src: bool) -> Vec<&T> {
        if n == 0 {
            if src {
                vec![self.elements.first().unwrap()]
            } else {
                vec![self.elements.last().unwrap()]
            }
        } else {
            self.elements
                .iter()
                .chain(self.branches.iter().flat_map(|br| br.bdry_set(n - 1, src)))
                .collect()
        }
    }

    pub(crate) fn get_maximal_elements(&self) -> Vec<&T> {
        if self.branches.is_empty() {
            vec![self.elements.last().unwrap().clone()]
        } else {
            self.branches
                .iter()
                .flat_map(|br| br.get_maximal_elements())
                .collect()
        }
    }

    pub(crate) fn get_maximal_paths(&self) -> Vec<Path> {
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

    pub(crate) fn get_maximal_with_branching(&self) -> Vec<(Path, usize, &T)> {
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

    pub(crate) fn get_paths(&self) -> Vec<(Path, &T)> {
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

    pub(crate) fn singleton(i: T) -> Self {
        Tree {
            elements: vec![i],
            branches: vec![],
        }
    }

    pub(crate) fn label_from_max<S>(
        &self,
        iter: &mut impl Iterator<Item = S>,
    ) -> Option<Tree<NoDispOption<S>>> {
        if self.branches.is_empty() {
            return iter.next().map(|i| Tree::singleton(NoDispOption(Some(i))));
        }
        let branches = self
            .branches
            .iter()
            .map(|tr| tr.label_from_max(iter))
            .collect::<Option<Vec<_>>>()?;

        let elements = self.elements.iter().map(|_| NoDispOption(None)).collect();

        Some(Tree { elements, branches })
    }

    pub(crate) fn map_ref<U, S>(&self, f: &U) -> Tree<S>
    where
        U: Fn(&T) -> S,
    {
        let branches = self.branches.iter().map(|br| br.map_ref(f)).collect();
        let elements = self.elements.iter().map(f).collect();
        Tree { branches, elements }
    }

    pub(crate) fn map<U, S>(self, f: &U) -> Tree<S>
    where
        U: Fn(T) -> S,
    {
        let branches = self.branches.into_iter().map(|br| br.map(f)).collect();
        let elements = self.elements.into_iter().map(f).collect();
        Tree { branches, elements }
    }

    pub(crate) fn path_tree(&self) -> Tree<Path> {
        let elements = (0..self.elements.len()).map(Path::here).collect();
        let branches = self
            .branches
            .iter()
            .enumerate()
            .map(|(i, br)| br.path_tree().map(&|p| p.extend(i)))
            .collect();

        Tree { elements, branches }
    }

    pub(crate) fn lookup(&self, p: &Path) -> Option<&T> {
        let mut tr = self;
        for x in p.path.iter().rev() {
            tr = tr.branches.get(*x)?;
        }
        tr.elements.get(p.here)
    }

    pub(crate) fn insertion(&mut self, mut bp: Path, inner: Tree<T>) {
        match bp.path.pop() {
            Some(i) => {
                self.branches[i].insertion(bp, inner.branches.into_iter().next().unwrap());
            }
            None => {
                self.elements.splice(bp.here..bp.here + 2, inner.elements);
                self.branches.splice(bp.here..bp.here + 1, inner.branches);
            }
        }
    }

    pub(crate) fn unwrap_disc(self) -> T {
        if self.branches.is_empty() {
            self.elements.into_iter().next().unwrap()
        } else {
            self.branches.into_iter().next().unwrap().unwrap_disc()
        }
    }

    pub(crate) fn bdry(&self, d: usize, tgt: bool) -> Tree<T>
    where
        T: Clone,
    {
        if d == 0 {
            if tgt {
                Tree::singleton(self.elements.last().unwrap().clone())
            } else {
                Tree::singleton(self.elements.first().unwrap().clone())
            }
        } else {
            Tree {
                elements: self.elements.clone(),
                branches: self.branches.iter().map(|br| br.bdry(d - 1, tgt)).collect(),
            }
        }
    }

    pub(crate) fn has_trunk_height(&self, height: usize) -> bool {
        height == 0
            || self
                .branches
                .iter()
                .exactly_one()
                .is_ok_and(|br| br.has_trunk_height(height - 1))
    }
}

impl<T: Default> Tree<T> {
    pub(crate) fn disc(n: usize) -> Self {
        if n == 0 {
            Tree::singleton(T::default())
        } else {
            Tree {
                elements: vec![T::default(), T::default()],
                branches: vec![Self::disc(n - 1)],
            }
        }
    }

    pub(crate) fn susp(self) -> Self {
        Tree {
            elements: vec![Default::default(), Default::default()],
            branches: vec![self],
        }
    }
}

pub trait Container<P, T> {
    fn idx(&self, pos: &P) -> &T;

    fn to_tree_or_vec(&self) -> Either<&Tree<T>, &Vec<T>>;
}

pub trait Ctx<P: Position> {
    fn susp_ctx(self) -> Self;

    fn get_name(&self, pos: &P) -> Option<Name>;

    fn id_sem_ctx(&self) -> SemCtx<P, P>;

    fn check_in_tree<F, S>(
        &self,
        term: &TermR<S>,
        func: F,
    ) -> Result<(TermC<P>, TypeC<P>), TypeCheckError<S>>
    where
        F: FnOnce(
            &Tree<NoDispOption<Name>>,
        ) -> Result<(TermC<Path>, TypeC<Path>), TypeCheckError<S>>,
        S: Clone;
}

pub trait Position: Clone + PartialEq + Eq {
    type Container<T: Clone>: Container<Self, T> + Clone;
    type Ctx: Ctx<Self> + Clone;

    fn to_name(&self) -> Name;
}

pub trait Eval: Position {
    fn eval<T: Clone>(tm: &TermC<Self>, ctx: &SemCtx<Self, T>, env: &Environment) -> TermN<T>;

    fn eval_args<T: Eval, U: Clone>(
        args: &ArgsC<Self, T>,
        ty: &TypeC<T>,
        ctx: &SemCtx<T, U>,
        env: &Environment,
    ) -> SemCtx<Self, U>;

    fn restrict<T: Clone>(ctx: SemCtx<Self, T>) -> SemCtx<Self, T>;
}

pub type Level = usize;

impl<T> Container<Level, T> for Vec<T> {
    fn idx(&self, pos: &usize) -> &T {
        self.get(*pos).unwrap()
    }

    fn to_tree_or_vec(&self) -> Either<&Tree<T>, &Vec<T>> {
        Either::Right(self)
    }
}

impl Ctx<Level> for Vec<(Option<Name>, TypeC<Level>)> {
    fn susp_ctx(self) -> Self {
        let mut new_ctx = vec![(None, TypeC::Base), (None, TypeC::Base)];
        new_ctx.extend(self);
        new_ctx
    }

    fn get_name(&self, pos: &Level) -> Option<Name> {
        self.get(*pos).and_then(|x| x.0.clone())
    }

    fn id_sem_ctx(&self) -> SemCtx<usize, usize> {
        SemCtx::id_vec(self.len())
    }

    fn check_in_tree<F, S>(
        &self,
        term: &TermR<S>,
        _: F,
    ) -> Result<(TermC<Level>, TypeC<Level>), TypeCheckError<S>>
    where
        F: FnOnce(
            &Tree<NoDispOption<Name>>,
        ) -> Result<(TermC<Path>, TypeC<Path>), TypeCheckError<S>>,
        S: Clone,
    {
        Err(TypeCheckError::CannotCheckCtx(term.clone()))
    }
}

impl Position for Level {
    type Container<T: Clone> = Vec<T>;

    type Ctx = Vec<(Option<Name>, TypeC<Level>)>;

    fn to_name(&self) -> Name {
        Name(format!("l{}", self))
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Path {
    pub(crate) here: usize,
    pub(crate) path: Vec<usize>,
}

impl Ctx<Path> for Tree<NoDispOption<Name>> {
    fn susp_ctx(self) -> Self {
        self.susp()
    }

    fn get_name(&self, pos: &Path) -> Option<Name> {
        self.lookup(pos).and_then(|x| x.0.clone())
    }

    fn id_sem_ctx(&self) -> SemCtx<Path, Path> {
        SemCtx::id_tree(self)
    }

    fn check_in_tree<F, S>(
        &self,
        _: &TermR<S>,
        func: F,
    ) -> Result<(TermC<Path>, TypeC<Path>), TypeCheckError<S>>
    where
        F: FnOnce(
            &Tree<NoDispOption<Name>>,
        ) -> Result<(TermC<Path>, TypeC<Path>), TypeCheckError<S>>,
        S: Clone,
    {
        func(self)
    }
}

impl<T> Container<Path, T> for Tree<T> {
    fn idx(&self, p: &Path) -> &T {
        let mut tr = self;
        for x in p.path.iter().rev() {
            tr = &tr.branches[*x];
        }
        &tr.elements[p.here]
    }

    fn to_tree_or_vec(&self) -> Either<&Tree<T>, &Vec<T>> {
        Either::Left(self)
    }
}

impl Position for Path {
    type Container<T: Clone> = Tree<T>;

    type Ctx = Tree<NoDispOption<Name>>;

    fn to_name(&self) -> Name {
        Name(format!("p{}", self))
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for x in self.path.iter().rev() {
            write!(f, "{x}")?;
        }
        write!(f, "{}", self.here)
    }
}

impl Path {
    pub(crate) fn here(n: usize) -> Self {
        Path {
            here: n,
            path: vec![],
        }
    }

    pub(crate) fn extend(mut self, n: usize) -> Path {
        self.path.push(n);
        self
    }

    pub(crate) fn to_type(&self) -> TypeC<Path> {
        let mut ty = TypeC::Base;
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

            current_path.insert(0, *x);

            ty = TypeC::Arr(TermC::Var(fst), Box::new(ty), TermC::Var(snd))
        }
        ty
    }

    pub(crate) fn fst_mut(&mut self) -> &mut usize {
        self.path.last_mut().unwrap_or(&mut self.here)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Insertion {
    Pruning,
    Full,
}

pub struct Reduction {
    pub disc_rem: bool,
    pub endo_coh: bool,
    pub insertion: Option<Insertion>,
}

pub enum Support {
    FullInverse,
    NoInverse,
}

#[derive(Clone)]
pub struct InferRes<T: Position> {
    pub(crate) ctx: <T as Position>::Ctx,
    pub(crate) tm: TermC<T>,
    pub(crate) ty: TypeC<T>,
}

impl<T: Position> InferRes<T> {
    pub(crate) fn susp(self) -> Self {
        InferRes {
            ctx: self.ctx.susp_ctx(),
            tm: TermC::Susp(Box::new(self.tm)),
            ty: TypeC::Susp(Box::new(self.ty)),
        }
    }
}

pub type InferResEither = Either<InferRes<Path>, InferRes<Level>>;

pub struct Environment {
    pub top_level: HashMap<Name, InferResEither>,
    pub reduction: Reduction,
    pub support: Support,
    pub implicits: bool,
}
