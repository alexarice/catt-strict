use std::ops::RangeInclusive;

use itertools::Itertools;

use crate::{
    common::{
        Container, Environment, Eval, Insertion, Level, Name, NoDispOption, Path, Position, Tree,
    },
    syntax::core::{ArgsC, ArgsWithTypeC, TermC, TypeC},
    syntax::normal::{HeadN, TermN, TypeN},
};

#[derive(Clone, Debug)]
pub struct SemCtx<S: Position, T: Clone> {
    map: S::Container<TermN<T>>,
    ty: TypeN<T>,
}

impl<S: Position, T: Clone> SemCtx<S, T> {
    pub(crate) fn new(map: S::Container<TermN<T>>, ty: TypeN<T>) -> Self {
        SemCtx { map, ty }
    }

    pub(crate) fn get(&self, pos: &S) -> TermN<T> {
        self.map.idx(pos).clone()
    }

    pub(crate) fn get_ty(&self) -> TypeN<T> {
        self.ty.clone()
    }
}

impl<S: Eval, T: Clone> SemCtx<S, T> {
    pub(crate) fn restrict(self) -> Self {
        S::restrict(self)
    }
}

impl SemCtx<Path, Path> {
    pub(crate) fn id_tree<U>(positions: &Tree<U>) -> Self {
        SemCtx::new(positions.path_tree().map(&TermN::Variable), TypeN::base())
    }
}

impl SemCtx<Level, Level> {
    pub(crate) fn id_vec(len: usize) -> Self {
        SemCtx::new((0..len).map(TermN::Variable).collect(), TypeN::base())
    }
}

impl<T: Clone> SemCtx<Path, T> {
    pub(crate) fn include(mut self, rng: &RangeInclusive<usize>) -> Self {
        let map = Tree {
            elements: self.map.elements.drain(rng.clone()).collect(),
            branches: self.map.branches.drain(rng.start()..rng.end()).collect(),
        };

        SemCtx { ty: self.ty, map }
    }

    pub(crate) fn into_args(self) -> (Tree<TermN<T>>, usize) {
        let dim = self.ty.dim();

        (self.map.unrestrict(self.ty), dim)
    }
}

impl<T> Tree<TermN<T>> {
    pub(crate) fn unrestrict(mut self, ty: TypeN<T>) -> Self {
        for (s, t) in ty.0.into_iter().rev() {
            self = Tree {
                elements: vec![s, t],
                branches: vec![self],
            };
        }
        self
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn find_insertion_redex(
        &self,
        insertion: &Insertion,
    ) -> Option<(Path, Tree<NoDispOption<Name>>, Tree<TermN<T>>)>
    where
        T: Clone,
    {
        let v = self.get_maximal_with_branching();
        v.into_iter().find_map(|(p, bh, tm)| match tm {
            TermN::Other(HeadN::IdN { dim }, args) => Some((p, Tree::disc(*dim), args.clone())),
            TermN::Other(HeadN::CompN { tree }, args) if insertion == &Insertion::Full => tree
                .has_trunk_height(bh)
                .then_some((p, tree.clone(), args.clone())),
            _ => None,
        })
    }
}

fn eval_coh<T: Clone>(
    mut tree: Tree<NoDispOption<Name>>,
    mut tyt: Option<TypeC<Path>>,
    ctx: &SemCtx<Path, T>,
    env: &Environment,
) -> TermN<T> {
    let (mut args, dim) = ctx.clone().into_args();

    let final_dim = tree.dim() + dim;

    for _ in 0..dim {
        tree = tree.susp();
        tyt = tyt.map(|x| TypeC::Susp(Box::new(x)))
    }

    if let Some(insertion) = &env.reduction.insertion {
        while let Some((p, tr, args_inner)) = args.find_insertion_redex(insertion) {
            tyt = tyt.map(|x| {
                let l = tree.exterior_sub(p.clone(), &tr);
                TypeC::AppPath(
                    Box::new(x),
                    ArgsWithTypeC {
                        args: l,
                        ty: Box::new(TypeC::Base),
                    },
                )
            });

            tree.insertion(p.clone(), tr);
            args.insertion(p.clone(), args_inner);
        }
    }

    let tyn = tyt.map_or_else(
        || {
            tree.standard_type(final_dim)
                .eval(&SemCtx::id_tree(&tree), env)
        },
        |x| x.eval(&SemCtx::id_tree(&tree), env),
    );

    if env.reduction.endo_coh && tyn.0.last().is_some_and(|(s, t)| s == t) {
        if let TypeC::Arr(s, a, _) = tyn.quote() {
            let sem_ctx = SemCtx::new(args, TypeN::base());

            let args = s.eval(&sem_ctx, env).into_args(a.eval(&sem_ctx, env));

            return TermN::Other(HeadN::IdN { dim: tyn.dim() - 1 }, args);
        }
    }

    if !env.reduction.endo_coh && tree.is_disc() {
        let path = tree.get_maximal_paths().into_iter().next().unwrap();
        let term = TermN::Variable(path);
        if tyn.0.last().is_some_and(|(s, t)| s == &term && t == &term) {
            return TermN::Other(HeadN::IdN { dim: tree.dim() }, args);
        }
    }

    if tyn.is_standard(&tree) {
        if env.reduction.disc_rem && tree.is_disc() {
            return args.unwrap_disc();
        }
        return TermN::Other(HeadN::CompN { tree }, args);
    }

    TermN::Other(HeadN::CohN { tree, ty: tyn }, args)
}

impl Eval for Path {
    fn eval<T: Clone>(tm: &TermC<Self>, ctx: &SemCtx<Self, T>, env: &Environment) -> TermN<T> {
        match tm {
            TermC::AppLvl(t, awt) => {
                let sem_ctx = awt.eval(ctx, env);
                t.eval(&sem_ctx, env)
            }
            TermC::AppPath(t, awt) => {
                let sem_ctx = awt.eval(ctx, env);
                t.eval(&sem_ctx, env)
            }
            TermC::Var(pos) => ctx.get(pos).clone(),
            TermC::TopLvl(_, tmt) => tmt.eval(ctx, env),
            TermC::Susp(t) => t.eval(&ctx.clone().restrict(), env),
            TermC::Include(t, rng) => t.eval(&ctx.clone().include(rng), env),
            TermC::Comp(tr) => eval_coh(tr.clone(), None, ctx, env),
            TermC::Coh(tr, ty) => eval_coh(tr.clone(), Some(*ty.clone()), ctx, env),
            TermC::Id(dim) => {
                let (args, res_dim) = ctx.clone().into_args();
                TermN::Other(HeadN::IdN { dim: res_dim + dim }, args)
            }
        }
    }

    fn eval_args<T: Eval, U: Clone>(
        args: &ArgsC<Self, T>,
        ty: &TypeC<T>,
        ctx: &SemCtx<T, U>,
        env: &Environment,
    ) -> SemCtx<Self, U> {
        let map = args.map_ref(&|tm| tm.eval(ctx, env));

        let tyn = ty.eval(ctx, env);
        SemCtx::new(map, tyn)
    }

    fn restrict<T: Clone>(mut ctx: SemCtx<Self, T>) -> SemCtx<Self, T> {
        ctx.ty
            .0
            .push(ctx.map.elements.into_iter().next_tuple().unwrap());

        ctx.map = ctx.map.branches.into_iter().next().unwrap();

        ctx
    }
}

impl Eval for Level {
    fn eval<T: Clone>(tm: &TermC<Self>, ctx: &SemCtx<Self, T>, env: &Environment) -> TermN<T> {
        match tm {
            TermC::AppLvl(t, awt) => {
                let sem_ctx = awt.eval(ctx, env);
                t.eval(&sem_ctx, env)
            }
            TermC::AppPath(t, awt) => {
                let sem_ctx = awt.eval(ctx, env);
                t.eval(&sem_ctx, env)
            }
            TermC::Var(pos) => ctx.get(pos).clone(),
            TermC::TopLvl(_, tmt) => tmt.eval(ctx, env),
            TermC::Susp(t) => t.eval(&ctx.clone().restrict(), env),
            _ => unreachable!(),
        }
    }

    fn eval_args<T: Eval, U: Clone>(
        args: &ArgsC<Self, T>,
        ty: &TypeC<T>,
        ctx: &SemCtx<T, U>,
        env: &Environment,
    ) -> SemCtx<Self, U> {
        let map = args.iter().map(|t| t.eval(ctx, env)).collect();
        let tyn = ty.eval(ctx, env);
        SemCtx::new(map, tyn)
    }

    fn restrict<T: Clone>(mut ctx: SemCtx<Self, T>) -> SemCtx<Self, T> {
        ctx.ty.0.push(ctx.map.drain(0..2).next_tuple().unwrap());
        ctx
    }
}

impl<S: Eval> TermC<S> {
    pub(crate) fn eval<T: Clone>(&self, ctx: &SemCtx<S, T>, env: &Environment) -> TermN<T> {
        S::eval(self, ctx, env)
    }
}

impl<S: Eval> TypeC<S> {
    pub(crate) fn eval<T: Clone>(&self, ctx: &SemCtx<S, T>, env: &Environment) -> TypeN<T> {
        match &self {
            TypeC::Base => ctx.get_ty().clone(),
            TypeC::Arr(s, a, t) => {
                let mut an = a.eval(ctx, env);
                an.0.push((s.eval(ctx, env), t.eval(ctx, env)));
                an
            }
            TypeC::AppLvl(ty, awt) => ty.eval(&awt.eval(ctx, env), env),
            TypeC::AppPath(ty, awt) => ty.eval(&awt.eval(ctx, env), env),
            TypeC::Susp(ty) => {
                let new_ctx: SemCtx<S, T> = ctx.clone();
                ty.eval(&new_ctx.restrict(), env)
            }
        }
    }
}

impl<S: Eval, T: Eval> ArgsWithTypeC<S, T> {
    pub(crate) fn eval<U: Clone>(&self, ctx: &SemCtx<T, U>, env: &Environment) -> SemCtx<S, U> {
        S::eval_args(&self.args, &self.ty, ctx, env)
    }
}

impl Tree<NoDispOption<Name>> {
    fn standard(self, d: usize) -> Tree<TermC<Path>> {
        let mut ty = self.standard_type(d);
        let mut tr = Tree::singleton(self.standard_comp(d));
        while let TypeC::Arr(s, a, t) = ty {
            tr = Tree {
                elements: vec![s, t],
                branches: vec![tr],
            };
            ty = *a;
        }
        tr
    }

    fn exterior_sub(&self, mut bp: Path, inner: &Tree<NoDispOption<Name>>) -> Tree<TermC<Path>> {
        match bp.path.pop() {
            Some(i) => {
                let mut l = self.path_tree().map(&TermC::Var);

                l.branches[i] = self.branches[i]
                    .exterior_sub(bp, &inner.branches[0])
                    .map(&|tm| TermC::Include(Box::new(TermC::Susp(Box::new(tm))), i..=i + 1));

                l
            }
            None => {
                let inner_size = inner.branches.len();
                let mut l = self.path_tree().map(&|mut p| {
                    let i = p.fst_mut();
                    if *i > bp.here {
                        *i += inner_size;
                        *i -= 1;
                    }
                    TermC::Var(p)
                });

                let d = self.branches[bp.here].dim() + 1;
                let inner_args = inner
                    .clone()
                    .standard(d)
                    .map(&|tm| TermC::Include(Box::new(tm), bp.here..=bp.here + inner_size));
                l.branches.splice(bp.here..bp.here + 1, inner_args.branches);

                l
            }
        }
    }
}
