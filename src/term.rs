use std::ops::RangeInclusive;

use derivative::Derivative;
use either::Either;

use crate::{
    common::{Container, CtxT, Level, Name, NoDispOption, Path, Position, Spanned, Tree},
    syntax::{ArgsE, ArgsWithTypeE, TermE, TypeE},
};

#[derive(Clone, Debug, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum TermT<T: Clone> {
    AppLvl(Box<TermT<Level>>, ArgsWithTypeT<Level, T>),
    AppPath(Box<TermT<Path>>, ArgsWithTypeT<Path, T>),
    Var(T),
    TopLvl(Name, Box<TermT<T>>),
    Susp(Box<TermT<T>>),
    Coh(Tree<NoDispOption<Name>>, Box<TypeT<Path>>),
    Include(Box<TermT<T>>, RangeInclusive<usize>),
    Comp(Tree<NoDispOption<Name>>),
    Id(usize),
}

pub type ArgsT<S, T> = <S as Position>::Container<TermT<T>>;

#[derive(Derivative, Clone)]
#[derivative(
    Debug(bound = "T: std::fmt::Debug, ArgsT<S,T>: std::fmt::Debug"),
    PartialEq(bound = "T: PartialEq, ArgsT<S,T>: PartialEq"),
    Eq(bound = "T: Eq, ArgsT<S,T>: Eq")
)]
pub struct ArgsWithTypeT<S: Position, T: Clone> {
    pub(crate) args: ArgsT<S, T>,
    pub(crate) ty: Box<TypeT<T>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeT<T: Clone> {
    Base,
    Arr(TermT<T>, Box<TypeT<T>>, TermT<T>),
    AppLvl(Box<TypeT<Level>>, ArgsWithTypeT<Level, T>),
    AppPath(Box<TypeT<Path>>, ArgsWithTypeT<Path, T>),
    Susp(Box<TypeT<T>>),
}

impl<T: Position> TermT<T> {
    pub(crate) fn to_expr(&self, ctx: Option<&T::Ctx>, with_ict: bool) -> TermE<()> {
        match self {
            TermT::AppLvl(tm, args) => TermE::App(
                Box::new(tm.to_expr(None, with_ict)),
                args.to_expr(ctx, with_ict),
                (),
            ),
            TermT::AppPath(tm, args) => TermE::App(
                Box::new(tm.to_expr(None, with_ict)),
                args.to_expr(ctx, with_ict),
                (),
            ),
            TermT::Var(x) => TermE::Var(
                ctx.and_then(|c| c.get_name(x)).unwrap_or(x.to_name()),
                (),
            ),
            TermT::TopLvl(nm, _) => TermE::Var(nm.clone(), ()),
            TermT::Susp(t) => TermE::Susp(Box::new(t.to_expr(None, with_ict)), ()),
            TermT::Coh(tr, ty) => TermE::Coh(
                tr.clone(),
                Box::new(ty.to_expr(Some(&tr.clone()), with_ict)),
                (),
            ),
            TermT::Include(tm, rng) => {
                TermE::Include(Box::new(tm.to_expr(ctx, with_ict)), rng.clone(), ())
            }
            TermT::Comp(_) => TermE::Comp(()),
            TermT::Id(_) => TermE::Id(()),
        }
    }
}

impl<S: Position, T: Position> ArgsWithTypeT<S, T> {
    pub(crate) fn to_expr(&self, ctx: Option<&T::Ctx>, with_ict: bool) -> ArgsWithTypeE<()> {
        let args = match self.args.to_tree_or_vec() {
            Either::Right(s) => ArgsE::Sub(Spanned(
                s.iter().map(|tm| tm.to_expr(ctx, with_ict)).collect(),
                (),
            )),
            Either::Left(l) => ArgsE::Label(Spanned(
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
        };

        ArgsWithTypeE {
            args,
            ty: with_ict.then_some(Box::new(self.ty.to_expr(ctx, with_ict))),
        }
    }
}

impl<T: Position> TypeT<T> {
    pub(crate) fn to_expr(&self, ctx: Option<&T::Ctx>, with_ict: bool) -> TypeE<()> {
        match self {
            TypeT::Base => TypeE::Base(()),
            TypeT::Arr(s, a, t) => TypeE::Arr(
                s.to_expr(ctx, with_ict),
                with_ict.then_some(Box::new(a.to_expr(ctx, with_ict))),
                t.to_expr(ctx, with_ict),
                (),
            ),
            TypeT::AppLvl(ty, args) => TypeE::App(
                Box::new(ty.to_expr(None, with_ict)),
                args.to_expr(ctx, with_ict),
                (),
            ),
            TypeT::AppPath(ty, args) => TypeE::App(
                Box::new(ty.to_expr(None, with_ict)),
                args.to_expr(ctx, with_ict),
                (),
            ),
            TypeT::Susp(ty) => TypeE::Susp(Box::new(ty.to_expr(ctx, with_ict)), ()),
        }
    }
}

impl Tree<NoDispOption<Name>> {
    pub(crate) fn unbiased_comp(self, d: usize) -> TermT<Path> {
        let ty = self.unbiased_type(d);
        TermT::Coh(self, Box::new(ty))
    }
    pub(crate) fn unbiased_term(self, d: usize) -> TermT<Path> {
        if d == 0 {
            if self.branches.is_empty() {
                TermT::Var(Path::here(0))
            } else {
                self.unbiased_comp(d)
            }
        } else if self.branches.len() == 1 {
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

    pub(crate) fn unbiased_type(&self, d: usize) -> TypeT<Path> {
        if d == 0 {
            TypeT::Base
        } else {
            let ptree = self.path_tree().map(&TermT::Var);
            let src = self.bdry(d - 1, false);
            let tgt = self.bdry(d - 1, true);
            TypeT::Arr(
                TermT::AppPath(
                    Box::new(src.unbiased_term(d - 1)),
                    ArgsWithTypeT {
                        args: ptree.bdry(d - 1, false),
                        ty: Box::new(TypeT::Base),
                    },
                ),
                Box::new(self.unbiased_type(d - 1)),
                TermT::AppPath(
                    Box::new(tgt.unbiased_term(d - 1)),
                    ArgsWithTypeT {
                        args: ptree.bdry(d - 1, true),
                        ty: Box::new(TypeT::Base),
                    },
                ),
            )
        }
    }
}
