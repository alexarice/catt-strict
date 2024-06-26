use std::{collections::HashSet, ops::Deref};

use derivative::Derivative;
use ref_cast::RefCast;

use crate::common::{Name, NoDispOption, Path, Support, Tree};

#[derive(Clone, Debug, Eq, Derivative)]
#[derivative(PartialEq)]
pub enum HeadN {
    Coh {
        tree: Tree<NoDispOption<Name>>,
        ty: TypeN<Path>,
    },
    Comp {
        tree: Tree<NoDispOption<Name>>,
    },
    Id {
        dim: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermN<P> {
    Variable(P),
    Other(HeadN, Tree<TermN<P>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeN<P>(pub(crate) Vec<(TermN<P>, TermN<P>)>);

#[derive(Debug, PartialEq, Eq, RefCast)]
#[repr(transparent)]
pub struct TypeNRef<P>(pub(crate) [(TermN<P>, TermN<P>)]);

impl<P> Deref for TypeN<P> {
    type Target = TypeNRef<P>;

    fn deref(&self) -> &Self::Target {
        TypeNRef::ref_cast(&self.0)
    }
}

impl HeadN {
    pub(crate) fn size(&self) -> usize {
        match self {
            HeadN::Coh { ty, .. } => 1 + ty.size(),
            HeadN::Comp { .. } => 1,
            HeadN::Id { .. } => 1,
        }
    }
}

impl<P> TermN<P> {
    pub(crate) fn into_args(self, ty: TypeN<P>) -> Tree<TermN<P>> {
        ty.0.into_iter()
            .rfold(Tree::singleton(self), |tr, (s, t)| Tree {
                elements: vec![s, t],
                branches: vec![tr],
            })
    }

    pub(crate) fn size(&self) -> usize {
        match self {
            TermN::Variable(_) => 0,
            TermN::Other(h, tr) => {
                h.size()
                    + tr.get_paths()
                        .into_iter()
                        .map(|(_, tm)| tm.size())
                        .sum::<usize>()
            }
        }
    }
}

impl TermN<Path> {
    pub(crate) fn free_vars(&self, set: &mut HashSet<Path>) {
        match self {
            TermN::Variable(p) => {
                set.insert(p.clone());
            }
            TermN::Other(_, args) => {
                for (_, tm) in args.get_paths() {
                    tm.free_vars(set);
                }
            }
        }
    }
}

impl<P> TypeN<P> {
    pub(crate) fn base() -> TypeN<P> {
        TypeN(vec![])
    }

    pub(crate) fn dim(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn size(&self) -> usize {
        self.0.iter().map(|(s, t)| s.size() + t.size()).sum()
    }
}

impl TypeN<Path> {
    pub(crate) fn free_vars(self) -> HashSet<Path> {
        let mut set = HashSet::new();
        for (s, t) in self.0 {
            s.free_vars(&mut set);
            t.free_vars(&mut set);
        }
        set
    }

    pub(crate) fn support_check<T>(mut self, tree: &Tree<T>, support: &Support) -> bool {
        match support {
            Support::NoInverse => {
                if let Some((s, t)) = self.0.pop() {
                    let mut src = self.free_vars();
                    let dim = tree.dim();
                    if dim >= 1 {
                        let path_tree = tree.path_tree();
                        let mut tgt = src.clone();
                        s.free_vars(&mut src);
                        t.free_vars(&mut tgt);

                        if (path_tree
                            .bdry_set(dim - 1, true)
                            .into_iter()
                            .cloned()
                            .collect::<HashSet<_>>()
                            == src)
                            && (path_tree
                                .bdry_set(dim - 1, false)
                                .into_iter()
                                .cloned()
                                .collect::<HashSet<_>>()
                                == tgt)
                        {
                            return true;
                        }
                    } else {
                        s.free_vars(&mut src);
                    }
                    t.free_vars(&mut src);

                    tree.get_paths().into_iter().all(|(p, _)| src.contains(&p))
                } else {
                    false
                }
            }
            Support::FullInverse => true,
        }
    }

    pub(crate) fn is_standard<T>(&self, tree: &Tree<T>) -> bool {
        let dim = tree.dim();
        if dim != self.dim() {
            return false;
        }
        if let Some((s, t)) = self.0.last() {
            let path_tree = tree.path_tree().map(&TermN::Variable);
            let src = path_tree.bdry(dim - 1, false);
            let src_correct = if let Some(x) = src.get_max() {
                s == x
            } else if let TermN::Other(HeadN::Comp { .. }, args) = s {
                args == &src
            } else {
                false
            };
            if !src_correct {
                return false;
            }
            let tgt = path_tree.bdry(dim - 1, true);
            let tgt_correct = if let Some(x) = tgt.get_max() {
                t == x
            } else if let TermN::Other(HeadN::Comp { .. }, args) = t {
                args == &tgt
            } else {
                false
            };
            tgt_correct
        } else {
            true
        }
    }
}

impl<P> TypeNRef<P> {
    pub(crate) fn inner(&self) -> &Self {
        TypeNRef::ref_cast(&self.0[0..self.0.len() - 1])
    }
}
