use crate::common::{Tree, Name, NoDispOption, Pos};

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

#[derive(Clone, Debug)]
pub enum CtxN {
    Ctx(Vec<TypeN>),
    Tree(Tree<NoDispOption<Name>>),
}
