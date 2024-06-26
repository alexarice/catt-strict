use std::ops::RangeInclusive;

use derivative::Derivative;
use either::Either;

use super::raw::{ArgsR, ArgsWithTypeR, TermRS, TypeRS};
use crate::{
    common::{Container, Ctx, Level, Name, NoDispOption, Path, Position, Spanned, Tree},
    syntax::raw::{TermR, TypeR},
};

#[derive(Clone, Debug, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum TermC<P: Clone> {
    AppSub(Box<TermC<Level>>, ArgsWithTypeC<Level, P>),
    AppLabel(Box<TermC<Path>>, ArgsWithTypeC<Path, P>),
    Var(P),
    TopLvl(Name, Box<TermC<P>>),
    Susp(Box<TermC<P>>),
    Coh(Tree<NoDispOption<Name>>, Box<TypeC<Path>>),
    Include(Box<TermC<P>>, RangeInclusive<usize>),
    Comp(Tree<NoDispOption<Name>>),
    Id(usize),
}

pub type ArgsC<P, Q> = <P as Position>::Container<TermC<Q>>;

#[derive(Derivative, Clone)]
#[derivative(
    Debug(bound = "Q: std::fmt::Debug, ArgsC<P,Q>: std::fmt::Debug"),
    PartialEq(bound = "Q: PartialEq, ArgsC<P,Q>: PartialEq"),
    Eq(bound = "Q: Eq, ArgsC<P,Q>: Eq")
)]
pub struct ArgsWithTypeC<P: Position, Q: Clone> {
    pub(crate) args: ArgsC<P, Q>,
    pub(crate) ty: Box<TypeC<Q>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeC<P: Clone> {
    Base,
    Arr(TermC<P>, Box<TypeC<P>>, TermC<P>),
    AppLvl(Box<TypeC<Level>>, ArgsWithTypeC<Level, P>),
    AppPath(Box<TypeC<Path>>, ArgsWithTypeC<Path, P>),
    Susp(Box<TypeC<P>>),
}

impl<P: Position> TermC<P> {
    pub(crate) fn to_raw(&self, ctx: Option<&P::Ctx>, with_ict: bool) -> TermRS<()> {
        let tm = match self {
            TermC::AppSub(tm, args) => TermR::App(
                Box::new(tm.to_raw(None, with_ict)),
                args.to_raw(ctx, with_ict),
            ),
            TermC::AppLabel(tm, args) => TermR::App(
                Box::new(tm.to_raw(None, with_ict)),
                args.to_raw(ctx, with_ict),
            ),
            TermC::Var(x) => TermR::Var(ctx.and_then(|c| c.get_name(x)).unwrap_or(x.to_name())),
            TermC::TopLvl(nm, _) => TermR::Var(nm.clone()),
            TermC::Susp(t) => TermR::Susp(Box::new(t.to_raw(None, with_ict))),
            TermC::Coh(tr, ty) => {
                TermR::Coh(tr.clone(), Box::new(ty.to_raw(Some(&tr.clone()), with_ict)))
            }
            TermC::Include(tm, rng) => {
                TermR::Include(Box::new(tm.to_raw(ctx, with_ict)), rng.clone())
            }
            TermC::Comp(_) => TermR::Comp,
            TermC::Id(_) => TermR::Id,
        };
        Spanned(tm, ())
    }
}

impl<P: Position, Q: Position> ArgsWithTypeC<P, Q> {
    pub(crate) fn to_raw(&self, ctx: Option<&Q::Ctx>, with_ict: bool) -> ArgsWithTypeR<()> {
        let args = match self.args.to_tree_or_vec() {
            Either::Right(s) => ArgsR::Sub(s.iter().map(|tm| tm.to_raw(ctx, with_ict)).collect()),
            Either::Left(l) => ArgsR::Label(if !with_ict {
                l.label_from_max(
                    &mut l
                        .get_maximal_elements()
                        .into_iter()
                        .map(|tm| tm.to_raw(ctx, with_ict)),
                )
                .unwrap()
            } else {
                l.map_ref(&|tm| NoDispOption(Some(tm.to_raw(ctx, with_ict))))
            }),
        };

        ArgsWithTypeR {
            args,
            ty: with_ict.then_some(Box::new(self.ty.to_raw(ctx, with_ict))),
            sp: (),
        }
    }
}

impl<P: Position> TypeC<P> {
    pub(crate) fn to_raw(&self, ctx: Option<&P::Ctx>, with_ict: bool) -> TypeRS<()> {
        let ty = match self {
            TypeC::Base => TypeR::Base,
            TypeC::Arr(s, a, t) => TypeR::Arr(
                s.to_raw(ctx, with_ict),
                with_ict.then_some(Box::new(a.to_raw(ctx, with_ict))),
                t.to_raw(ctx, with_ict),
            ),
            TypeC::AppLvl(ty, args) => TypeR::App(
                Box::new(ty.to_raw(None, with_ict)),
                args.to_raw(ctx, with_ict),
            ),
            TypeC::AppPath(ty, args) => TypeR::App(
                Box::new(ty.to_raw(None, with_ict)),
                args.to_raw(ctx, with_ict),
            ),
            TypeC::Susp(ty) => TypeR::Susp(Box::new(ty.to_raw(ctx, with_ict))),
        };
        Spanned(ty, ())
    }
}

impl Tree<NoDispOption<Name>> {
    pub(crate) fn standard_comp(self, d: usize) -> TermC<Path> {
        let ty = self.standard_type(d);
        TermC::Coh(self, Box::new(ty))
    }
    pub(crate) fn standard_term(self, d: usize) -> TermC<Path> {
        if d == 0 {
            if self.branches.is_empty() {
                TermC::Var(Path::here(0))
            } else {
                self.standard_comp(d)
            }
        } else if self.branches.len() == 1 {
            TermC::Susp(Box::new(
                self.branches
                    .into_iter()
                    .next()
                    .unwrap()
                    .standard_term(d - 1),
            ))
        } else {
            self.standard_comp(d)
        }
    }

    pub(crate) fn standard_type(&self, d: usize) -> TypeC<Path> {
        if d == 0 {
            TypeC::Base
        } else {
            let ptree = self.path_tree().map(&TermC::Var);
            let src = self.bdry(d - 1, false);
            let tgt = self.bdry(d - 1, true);
            TypeC::Arr(
                TermC::AppLabel(
                    Box::new(src.standard_term(d - 1)),
                    ArgsWithTypeC {
                        args: ptree.bdry(d - 1, false),
                        ty: Box::new(TypeC::Base),
                    },
                ),
                Box::new(self.standard_type(d - 1)),
                TermC::AppLabel(
                    Box::new(tgt.standard_term(d - 1)),
                    ArgsWithTypeC {
                        args: ptree.bdry(d - 1, true),
                        ty: Box::new(TypeC::Base),
                    },
                ),
            )
        }
    }
}
