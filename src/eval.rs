use std::ops::RangeInclusive;

use itertools::Itertools;

use crate::{
    common::{Name, NoDispOption, Path, Pos, Tree},
    normal::{HeadN, TermN, TypeN, TypeNRef},
    term::{ArgsT, ArgsWithTypeT, CtxT, LabelT, TermT, TypeT},
    typecheck::{Environment, Insertion},
};

#[derive(Clone, Debug)]
pub(crate) enum SemCtxMap {
    LabelN(Tree<TermN>),
    SubN(Vec<TermN>),
}

#[derive(Clone, Debug)]
pub(crate) struct SemCtx {
    map: SemCtxMap,
    ty: TypeN,
}

impl SemCtx {
    pub(crate) fn new(map: SemCtxMap, ty: TypeN) -> Self {
        SemCtx { map, ty }
    }

    pub(crate) fn id(ctx: &CtxT) -> Self {
        match ctx {
            CtxT::Tree(tr) => Self::id_tree(tr),
            CtxT::Ctx(c) => Self::id_vec(c.len()),
        }
    }

    pub(crate) fn id_tree<T>(positions: &Tree<T>) -> Self {
        SemCtx::new(
            SemCtxMap::LabelN(
                positions
                    .path_tree()
                    .map(&|p| TermN::Variable(Pos::Path(p))),
            ),
            TypeN::base(),
        )
    }

    pub(crate) fn id_vec(len: usize) -> Self {
        SemCtx::new(
            SemCtxMap::SubN((0..len).map(|i| TermN::Variable(Pos::Level(i))).collect()),
            TypeN::base(),
        )
    }

    pub(crate) fn get(&self, pos: &Pos) -> TermN {
        match (&self.map, pos) {
            (SemCtxMap::LabelN(l), Pos::Path(p)) => l.get(p).clone(),
            (SemCtxMap::SubN(s), Pos::Level(l)) => s[*l].clone(),
            _ => panic!("Invalid get"),
        }
    }

    pub(crate) fn get_ty(&self) -> TypeN {
        self.ty.clone()
    }

    pub(crate) fn restrict(self) -> Self {
        if let SemCtxMap::LabelN(l) = self.map {
            let mut ty = self.ty;
            let (s, t) = l.elements.into_iter().next_tuple().unwrap();
            ty.0.push((s, t));

            let map = SemCtxMap::LabelN(l.branches.into_iter().next().unwrap());

            SemCtx { ty, map }
        } else {
            panic!("Tried to restrict non label")
        }
    }

    pub(crate) fn include(self, rng: &RangeInclusive<usize>) -> Self {
        if let SemCtxMap::LabelN(mut l) = self.map {
            let map = SemCtxMap::LabelN(Tree {
                elements: l.elements.drain(rng.clone()).collect(),
                branches: l.branches.drain(rng.start()..rng.end()).collect(),
            });

            SemCtx { ty: self.ty, map }
        } else {
            panic!("Tried to restrict non label")
        }
    }

    pub(crate) fn to_args(self) -> (Tree<TermN>, usize) {
        let SemCtxMap::LabelN(args) = self.map else {
	    panic!("Non tree sem ctx converted to args")
	};

        let dim = self.ty.dim();

        (args.unrestrict(self.ty), dim)
    }
}

impl Tree<TermN> {
    pub(crate) fn unrestrict(mut self, ty: TypeN) -> Self {
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
    ) -> Option<(Path, Tree<NoDispOption<Name>>, Tree<TermN>)> {
        let v = self.get_maximal_with_branching();
        v.into_iter().find_map(|(p, bh, tm)| match tm {
            TermN::Other(HeadN::IdN { dim }, args) => Some((p, Tree::disc(*dim), args.clone())),
            TermN::Other(HeadN::UCohN { tree }, args) if insertion == &Insertion::Full => tree
                .has_trunk_height(bh)
                .then_some((p, tree.clone(), args.clone())),
            _ => None,
        })
    }
}

fn eval_coh(
    mut tree: Tree<NoDispOption<Name>>,
    mut tyt: Option<TypeT>,
    ctx: &SemCtx,
    env: &Environment,
) -> TermN {
    let (mut args, dim) = ctx.clone().to_args();

    let final_dim = tree.dim() + dim;

    for _ in 0..dim {
        tree = tree.susp();
        tyt = tyt.map(|x| TypeT::Susp(Box::new(x)))
    }

    if let Some(insertion) = &env.reduction.insertion {
        while let Some((p, tr, args_inner)) = args.find_insertion_redex(insertion) {
            tyt = tyt.map(|x| {
                let l = LabelT::exterior_sub(&tree, p.clone(), &tr);
                TypeT::App(
                    Box::new(x),
                    ArgsWithTypeT {
                        args: ArgsT::Label(l),
                        ty: Box::new(TypeT::Base),
                    },
                )
            });

            tree.insertion(p.clone(), tr);
            args.insertion(p.clone(), args_inner);
        }
    }

    let tyn = tyt.map_or_else(
        || {
            tree.unbiased_type(final_dim)
                .eval(&SemCtx::id_tree(&tree), env)
        },
        |x| x.eval(&SemCtx::id_tree(&tree), env),
    );

    if env.reduction.endo_coh && tyn.0.last().is_some_and(|(s, t)| s == t) {
        if let TypeT::Arr(s, a, _) = tyn.quote() {
            let sem_ctx = SemCtx::new(SemCtxMap::LabelN(args), TypeN::base());

            let args = s.eval(&sem_ctx, env).to_args(a.eval(&sem_ctx, env));

            return TermN::Other(HeadN::IdN { dim: tyn.dim() - 1 }, args);
        }
    }

    if !env.reduction.endo_coh && tree.is_disc() {
        let path = tree.get_maximal_paths().into_iter().next().unwrap();
        let term = TermN::Variable(Pos::Path(path));
        if tyn.0.last().is_some_and(|(s, t)| s == &term && t == &term) {
            return TermN::Other(HeadN::IdN { dim: tree.dim() }, args);
        }
    }

    if tyn.is_unbiased(&tree) {
        if env.reduction.disc_rem && tree.is_disc() {
            return args.unwrap_disc();
        }
        return TermN::Other(HeadN::UCohN { tree }, args);
    }

    TermN::Other(HeadN::CohN { tree, ty: tyn }, args)
}

impl TermT {
    pub(crate) fn eval(&self, ctx: &SemCtx, env: &Environment) -> TermN {
        match self {
            TermT::App(t, awt) => {
                let sem_ctx = awt.eval(ctx, env);
                t.eval(&sem_ctx, env)
            }
            TermT::Var(pos) => ctx.get(pos).clone(),
            TermT::TopLvl(name) => env.top_level.get(name).unwrap().1.eval(ctx, env),
            TermT::Susp(t) => t.eval(&ctx.clone().restrict(), env),
            TermT::Include(t, rng) => t.eval(&ctx.clone().include(rng), env),
            TermT::UComp(tr) => eval_coh(tr.clone(), None, ctx, env),
            TermT::Coh(tr, ty) => eval_coh(tr.clone(), Some(*ty.clone()), ctx, env),
            TermT::IdT(dim) => {
                let (args, res_dim) = ctx.clone().to_args();
                TermN::Other(HeadN::IdN { dim: res_dim + dim }, args)
            }
        }
    }
}

impl TypeT {
    pub(crate) fn eval(&self, ctx: &SemCtx, env: &Environment) -> TypeN {
        match &self {
            TypeT::Base => ctx.get_ty().clone(),
            TypeT::Arr(s, a, t) => {
                let mut an = a.eval(ctx, env);
                an.0.push((s.eval(ctx, env), t.eval(ctx, env)));
                an
            }
            TypeT::App(ty, awt) => ty.eval(&awt.eval(ctx, env), env),
            TypeT::Susp(ty) => ty.eval(&ctx.clone().restrict(), env),
        }
    }
}

impl ArgsWithTypeT {
    pub(crate) fn eval(&self, ctx: &SemCtx, env: &Environment) -> SemCtx {
        self.args.eval(&self.ty, ctx, env)
    }
}

impl ArgsT {
    pub(crate) fn eval(&self, ty: &TypeT, ctx: &SemCtx, env: &Environment) -> SemCtx {
        match self {
            ArgsT::Sub(ts) => {
                let map = SemCtxMap::SubN(ts.iter().map(|t| t.eval(ctx, env)).collect());
                let tyn = ty.eval(ctx, env);
                SemCtx::new(map, tyn)
            }
            ArgsT::Label(tr) => {
                let map = SemCtxMap::LabelN(tr.map_ref(&|tm| tm.eval(ctx, env)));

                let tyn = ty.eval(ctx, env);
                SemCtx::new(map, tyn)
            }
        }
    }
}

impl HeadN {
    pub(crate) fn quote(&self) -> TermT {
        match self {
            HeadN::CohN { tree, ty } => TermT::Coh(tree.clone(), Box::new(ty.quote())),
            HeadN::UCohN { tree } => TermT::UComp(tree.clone()),
            HeadN::IdN { dim } => TermT::IdT(*dim),
        }
    }
}

impl TermN {
    pub(crate) fn quote(&self) -> TermT {
        match self {
            TermN::Variable(x) => TermT::Var(x.clone()),
            TermN::Other(head, args) => TermT::App(
                Box::new(head.quote()),
                ArgsWithTypeT {
                    args: ArgsT::Label(args.map_ref(&|tm| tm.quote())),
                    ty: Box::new(TypeT::Base),
                },
            ),
        }
    }
}

impl TypeNRef {
    pub(crate) fn quote(&self) -> TypeT {
        let mut ret = TypeT::Base;

        for (s, t) in &self.0 {
            ret = TypeT::Arr(s.quote(), Box::new(ret), t.quote())
        }

        ret
    }
}

impl LabelT {
    pub(crate) fn unbiased(tree: Tree<NoDispOption<Name>>, d: usize) -> LabelT {
        let mut ty = tree.unbiased_type(d);
        let mut tr = Tree::singleton(tree.unbiased_comp(d));
        while let TypeT::Arr(s, a, t) = ty {
            tr = Tree {
                elements: vec![s, t],
                branches: vec![tr],
            };
            ty = *a;
        }
        tr
    }

    pub(crate) fn exterior_sub<T>(
        outer: &Tree<T>,
        mut bp: Path,
        inner: &Tree<NoDispOption<Name>>,
    ) -> LabelT {
        match bp.path.pop() {
            Some(i) => {
                let mut l = outer.path_tree().map(&|p| TermT::Var(Pos::Path(p)));

                l.branches[i] = LabelT::exterior_sub(&outer.branches[i], bp, &inner.branches[0])
                    .map(&|tm| TermT::Include(Box::new(TermT::Susp(Box::new(tm))), i..=i + 1));

                l
            }
            None => {
                let inner_size = inner.branches.len();
                let mut l = outer.path_tree().map(&|mut p| {
                    let i = p.fst_mut();
                    if *i > bp.here {
                        *i += inner_size;
                        *i -= 1;
                    }
                    TermT::Var(Pos::Path(p))
                });

                let d = outer.branches[bp.here].dim() + 1;
                let inner_args = LabelT::unbiased(inner.clone(), d)
                    .map(&|tm| TermT::Include(Box::new(tm), bp.here..=bp.here + inner_size));
                l.branches.splice(bp.here..bp.here + 1, inner_args.branches);

                l
            }
        }
    }
}
