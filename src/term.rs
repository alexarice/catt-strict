use std::ops::RangeInclusive;

use derivative::Derivative;

use crate::{
    common::{Name, NoDispOption, Path, Pos, Spanned, Tree},
    syntax::{Args, ArgsWithType, Term, Type},
};

#[derive(Clone, Debug, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum TermT {
    App(Box<TermT>, ArgsWithTypeT),
    Var(Pos),
    TopLvl(Name),
    Susp(Box<TermT>),
    Coh(Tree<NoDispOption<Name>>, Box<TypeT>),
    Include(Box<TermT>, RangeInclusive<usize>),
    UComp(Tree<NoDispOption<Name>>),
    IdT(usize),
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
    pub(crate) args: ArgsT,
    pub(crate) ty: Box<TypeT>,
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
    pub(crate) fn get_name(&self, p: &Pos) -> Option<Name> {
        match (self, p) {
            (CtxT::Tree(tr), Pos::Path(x)) => tr.lookup(x).and_then(|x| x.0.clone()),
            (CtxT::Ctx(ctx), Pos::Level(l)) => ctx.get(*l).and_then(|x| x.0.clone()),
            _ => None,
        }
    }
}

impl TermT {
    pub(crate) fn to_expr(&self, ctx: Option<&CtxT>, with_ict: bool) -> Term<()> {
        match self {
            TermT::App(tm, args) => Term::App(
                Box::new(tm.to_expr(None, with_ict)),
                args.to_expr(ctx, with_ict),
                (),
            ),
            TermT::Var(x) => Term::Var(
                ctx.and_then(|c| c.get_name(x))
                    .unwrap_or(Name(x.to_string())),
                (),
            ),
            TermT::TopLvl(nm) => Term::Var(nm.clone(), ()),
            TermT::Susp(t) => Term::Susp(Box::new(t.to_expr(None, with_ict)), ()),
            TermT::Coh(tr, ty) => Term::Coh(
                tr.clone(),
                Box::new(ty.to_expr(Some(&CtxT::Tree(tr.clone())), with_ict)),
                (),
            ),
            TermT::Include(tm, rng) => {
                Term::Include(Box::new(tm.to_expr(ctx, with_ict)), rng.clone(), ())
            }
            TermT::UComp(_) => Term::UComp(()),
            TermT::IdT(_) => Term::Id(()),
        }
    }
}

impl ArgsT {
    pub(crate) fn to_expr(&self, ctx: Option<&CtxT>, with_ict: bool) -> Args<()> {
        match self {
            ArgsT::Sub(s) => Args::Sub(Spanned(
                s.iter().map(|tm| tm.to_expr(ctx, with_ict)).collect(),
                (),
            )),
            ArgsT::Label(l) => Args::Label(Spanned(
                if !with_ict {
                    l.label_from_max(
                        &mut l
                            .get_maximal_elements()
                            .into_iter()
                            .map(|tm| tm.to_expr(ctx, with_ict)),
                    )
                    .unwrap()
                } else {
                    l.map_ref(&|tm| NoDispOption(Some(tm.to_expr(ctx, with_ict))))
                },
                (),
            )),
        }
    }
}

impl ArgsWithTypeT {
    pub(crate) fn to_expr(&self, ctx: Option<&CtxT>, with_ict: bool) -> ArgsWithType<()> {
        ArgsWithType {
            args: self.args.to_expr(ctx, with_ict),
            ty: with_ict.then_some(Box::new(self.ty.to_expr(ctx, with_ict))),
        }
    }
}

impl TypeT {
    pub(crate) fn to_expr(&self, ctx: Option<&CtxT>, with_ict: bool) -> Type<()> {
        match self {
            TypeT::Base => Type::Base(()),
            TypeT::Arr(s, a, t) => Type::Arr(
                s.to_expr(ctx, with_ict),
                with_ict.then_some(Box::new(a.to_expr(ctx, with_ict))),
                t.to_expr(ctx, with_ict),
                (),
            ),
            TypeT::App(ty, args) => Type::App(
                Box::new(ty.to_expr(None, with_ict)),
                args.to_expr(ctx, with_ict),
                (),
            ),
            TypeT::Susp(ty) => Type::Susp(Box::new(ty.to_expr(ctx, with_ict)), ()),
        }
    }
}

impl CtxT {
    pub(crate) fn susp(self) -> CtxT {
        match self {
            CtxT::Tree(tr) => {
                let new_tree = Tree {
                    elements: vec![NoDispOption::default(), NoDispOption::default()],
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

impl Tree<NoDispOption<Name>> {
    pub(crate) fn unbiased_comp(self, d: usize) -> TermT {
        let ty = self.unbiased_type(d);
        TermT::Coh(self, Box::new(ty))
    }
    pub(crate) fn unbiased_term(self, d: usize) -> TermT {
        if d == 0 {
            if self.branches.is_empty() {
                TermT::Var(Pos::Path(Path::here(0)))
            } else {
                self.unbiased_comp(d)
            }
        } else {
            if self.branches.len() == 1 {
                TermT::Susp(Box::new(
                    self.branches
                        .into_iter()
                        .next()
                        .unwrap()
                        .unbiased_term(d - 1),
                ))
            } else {
                self.unbiased_comp(d)
            }
        }
    }

    pub(crate) fn unbiased_type(&self, d: usize) -> TypeT {
        if d == 0 {
            TypeT::Base
        } else {
            let ptree = self.path_tree().map(&|p| TermT::Var(Pos::Path(p)));
            let src = self.bdry(d - 1, false);
            let tgt = self.bdry(d - 1, true);
            TypeT::Arr(
                TermT::App(
                    Box::new(src.unbiased_term(d - 1)),
                    ArgsWithTypeT {
                        args: ArgsT::Label(ptree.bdry(d - 1, false)),
                        ty: Box::new(TypeT::Base),
                    },
                ),
                Box::new(self.unbiased_type(d - 1)),
                TermT::App(
                    Box::new(tgt.unbiased_term(d - 1)),
                    ArgsWithTypeT {
                        args: ArgsT::Label(ptree.bdry(d - 1, true)),
                        ty: Box::new(TypeT::Base),
                    },
                ),
            )
        }
    }
}
