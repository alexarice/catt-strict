use crate::common::{Name, NoDispOption, Path, Pos, Tree};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeadN {
    pub tree: Tree<NoDispOption<Name>>,
    pub ty: TypeN,
    pub susp: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermN {
    Variable(Pos),
    Other(HeadN, Tree<TermN>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeN(pub Vec<(TermN, TermN)>);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CtxN {
    Ctx(Vec<TypeN>),
    Tree(Tree<NoDispOption<Name>>),
}

impl TermN {
    fn susp_level(&self) -> usize {
        match self {
            TermN::Variable(Pos::Path(p)) => p.path.len(),
            TermN::Variable(Pos::Level(_)) => 0,
            TermN::Other(h, a) => std::cmp::min(
                h.susp,
                a.get_maximal_elements()
                    .iter()
                    .map(|t| t.susp_level())
                    .min()
                    .unwrap(),
            ),
        }
    }

    fn de_susp_int(self, d: usize) -> TermN {
        match self {
            TermN::Variable(Pos::Path(p)) => TermN::Variable(Pos::Path(p.de_susp(d))),
            TermN::Variable(Pos::Level(_)) => unreachable!(),
            TermN::Other(h, a) => {
                let mut head = h;
                head.susp -= d;

                let mut args = a;
                for _ in 0..d {
                    args = args.branches.remove(0);
                }

                args = args.map(&|tm| tm.de_susp_int(d));

                TermN::Other(head, args)
            }
        }
    }

    pub fn susp(self) -> TermN {
        match self {
            TermN::Variable(p) => TermN::Variable(p.susp()),
            TermN::Other(mut head, args) => {
                head.susp += 1;
                TermN::Other(head, args.susp_args())
            }
        }
    }

    pub fn to_args(self, ty: TypeN) -> Tree<TermN> {
        ty.0.into_iter()
            .rfold(Tree::singleton(self), |tr, (s, t)| Tree {
                elements: vec![s, t],
                branches: vec![tr],
            })
    }
}

impl TypeN {
    pub fn base() -> TypeN {
        TypeN(vec![])
    }

    pub fn dim(&self) -> usize {
        self.0.len()
    }

    fn susp_level(&self) -> usize {
        match self.0.last() {
            Some((s, t)) => std::cmp::min(s.susp_level(), t.susp_level()),
            None => 0,
        }
    }

    fn de_susp_int(self, d: usize) -> TypeN {
        TypeN(
            self.0
                .into_iter()
                .skip(d)
                .map(|(s, t)| (s.de_susp_int(d), t.de_susp_int(d)))
                .collect(),
        )
    }

    pub fn de_susp(self, max: usize) -> (TypeN, usize) {
        let d = std::cmp::min(max, self.susp_level());

        let ty = if d == 0 { self } else { self.de_susp_int(d) };

        (ty, d)
    }

    pub fn susp(self) -> TypeN {
        let mut base = vec![(
            TermN::Variable(Pos::Path(Path::here(0))),
            TermN::Variable(Pos::Path(Path::here(1))),
        )];
        base.extend(self.0.into_iter().map(|(s, t)| (s.susp(), t.susp())));
        TypeN(base)
    }
}

impl Tree<TermN> {
    fn susp_args(self) -> Self {
        Tree {
            elements: vec![
                TermN::Variable(Pos::Path(Path::here(0))),
                TermN::Variable(Pos::Path(Path::here(1))),
            ],
            branches: vec![self.map(&|tm| tm.susp())],
        }
    }
}
