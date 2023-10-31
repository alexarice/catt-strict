use crate::common::{Name, NoDispOption, Path, Pos, Tree};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HeadN {
    Coh(Tree<NoDispOption<Name>>, Box<TypeN>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermN {
    Variable(Pos),
    Other(HeadN, Tree<TermN>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeN {
    Base,
    Arr(TermN, Box<TypeN>, TermN),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CtxN {
    Ctx(Vec<TypeN>),
    Tree(Tree<NoDispOption<Name>>),
}

impl TypeN {
    pub fn base(&self) -> Option<&TypeN> {
        match self {
            TypeN::Base => None,
            TypeN::Arr(_, a, _) => Some(a),
        }
    }
    pub fn dim(&self) -> usize {
        let mut ty = self;
        let mut dim = 0;
        while let Some(b) = ty.base() {
            ty = b;
            dim += 1;
        }
        dim
    }

    pub fn susp_base(n: usize) -> TypeN {
        if n <= 0 {
            TypeN::Base
        } else {
            TypeN::Arr(
                TermN::Variable(Pos::Path(Path(vec![0; n]))),
                Box::new(Self::susp_base(n - 1)),
                TermN::Variable(Pos::Path(Path(
                    std::iter::once(1).chain((0..).take(n - 1)).collect(),
                ))),
            )
        }
    }
}
