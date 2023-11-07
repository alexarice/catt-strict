use crate::common::{Name, NoDispOption, Pos, Tree};

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

impl TypeN {
    pub fn base() -> TypeN {
        TypeN(vec![])
    }

    pub fn dim(&self) -> usize {
        self.0.len()
    }
}
