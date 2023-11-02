use derivative::Derivative;

use crate::common::{Name, NoDispOption, Pos, Tree};

#[derive(Clone, Debug, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum TermT {
    App(Box<TermT>, ArgsWithTypeT),
    Var(Pos),
    TopLvl(Name),
    Susp(Box<TermT>),
    Coh(Tree<NoDispOption<Name>>, Box<TypeT>),
}

pub type SubT = Vec<TermT>;
pub type LabelT = Tree<TermT>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArgsT {
    Sub(SubT),
    Label(LabelT),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArgsWithTypeT {
    pub args: ArgsT,
    pub ty: Box<TypeT>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeT {
    Base,
    Arr(TermT, Box<TypeT>, TermT),
    App(Box<TypeT>, ArgsWithTypeT),
    Susp(Box<TypeT>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CtxT {
    Tree(Tree<NoDispOption<Name>>),
    Ctx(Vec<(Option<Name>, TypeT)>),
}

impl CtxT {
    pub fn susp(self) -> CtxT {
        match self {
            CtxT::Tree(tr) => {
                let new_tree = Tree {
                    elements: vec![NoDispOption(None), NoDispOption(None)],
                    branches: vec![tr],
                };
                CtxT::Tree(new_tree)
            }
            CtxT::Ctx(ctx) => {
                let mut new_ctx = vec![(None, TypeT::Base), (None, TypeT::Base)];
                new_ctx.extend(ctx);
                CtxT::Ctx(new_ctx)
            }
        }
    }
}
