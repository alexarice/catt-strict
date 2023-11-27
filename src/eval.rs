use std::{collections::HashMap, ops::RangeInclusive};

use crate::{
    common::{Name, NoDispOption, Path, Pos, Tree},
    normal::{HeadN, TermN, TypeN},
    term::{ArgsT, ArgsWithTypeT, LabelT, TermT, TypeT},
    typecheck::{Environment, Insertion},
};

#[derive(Clone, Debug)]
pub struct SemCtx {
    map: HashMap<Pos, TermN>,
    ty: TypeN,
}

impl SemCtx {
    pub fn new(map: HashMap<Pos, TermN>, ty: TypeN) -> Self {
        SemCtx { map, ty }
    }

    pub fn id(positions: impl IntoIterator<Item = Pos>) -> Self {
        SemCtx::new(
            positions
                .into_iter()
                .map(|pos| (pos.clone(), TermN::Variable(pos)))
                .collect(),
            TypeN::base(),
        )
    }

    pub fn get(&self, pos: &Pos) -> TermN {
        self.map.get(pos).cloned().unwrap()
    }

    pub fn get_ty(&self) -> TypeN {
        self.ty.clone()
    }

    pub fn restrict(mut self) -> Self {
        let mut ty = self.ty;
        ty.0.push((
            self.map
                .remove(&Pos::Path(Path::here(0)))
                .or(self.map.remove(&Pos::Level(0)))
                .unwrap(),
            self.map
                .remove(&Pos::Path(Path::here(1)))
                .or(self.map.remove(&Pos::Level(1)))
                .unwrap(),
        ));

        let map = self
            .map
            .into_iter()
            .map(|(pos, tm)| (pos.de_susp(), tm))
            .collect();

        SemCtx { ty, map }
    }

    pub fn include(self, rng: &RangeInclusive<usize>) -> Self {
        let map = self
            .map
            .into_iter()
            .filter_map(|(pos, tm)| match pos {
                Pos::Level(_) => None,
                Pos::Path(mut p) => {
                    let i = p.fst_mut();

                    if rng.contains(i) {
                        *i -= *rng.start();
                    } else {
                        return None;
                    }

                    Some((Pos::Path(p), tm))
                }
            })
            .collect();

        SemCtx { ty: self.ty, map }
    }
}

impl Tree<TermN> {
    pub fn unrestrict(mut self, ty: TypeN) -> Self {
        for (s, t) in ty.0.into_iter().rev() {
            self = Tree {
                elements: vec![s, t],
                branches: vec![self],
            };
        }
        self
    }

    #[allow(clippy::type_complexity)]
    pub fn find_insertion_redex(
        &self,
        insertion: &Insertion,
    ) -> Option<(Path, Tree<NoDispOption<Name>>, TypeN, Tree<TermN>)> {
        let v = self.get_maximal_with_branching();
        v.into_iter().find_map(|(p, bh, tm)| match tm {
            TermN::Variable(_) => None,
            TermN::Other(head, args) => {
                if head.susp < bh
                    || (matches!(insertion, Insertion::Pruning)
                        && (head.tree.dim() != 0
                            || head.ty
                                != TypeN(vec![(
                                    TermN::Variable(Pos::Path(Path::here(0))),
                                    TermN::Variable(Pos::Path(Path::here(1))),
                                )])))
                {
                    None
                } else {
                    let susp_amount = head.susp - bh;
                    let mut tree = head.tree.clone();
                    let mut ty = head.ty.clone();
                    for _ in 0..susp_amount {
                        tree = tree.susp();
                        ty = ty.susp();
                    }
                    let mut new_args = args.clone();

                    for _ in 0..bh {
                        new_args = new_args.branches.into_iter().next().unwrap();
                    }

                    Some((p, tree, ty, new_args))
                }
            }
        })
    }
}

fn eval_coh(
    mut tree: Tree<NoDispOption<Name>>,
    mut tyt: TypeT,
    ctx: &SemCtx,
    env: &Environment,
) -> TermN {
    let sem_ty = ctx.get_ty();
    let dim = sem_ty.dim();

    let mut args = tree
        .path_tree()
        .map(&|p| ctx.get(&Pos::Path(p)))
        .unrestrict(sem_ty);

    for _ in 0..dim {
        tree = tree.susp();
        tyt = TypeT::Susp(Box::new(tyt));
    }

    if let Some(insertion) = &env.reduction.insertion {
        while let Some((p, tr, ty_inner, args_inner)) = args.find_insertion_redex(insertion) {
            tyt = TypeT::App(
                Box::new(tyt),
                ArgsWithTypeT {
                    args: ArgsT::Label(LabelT::exterior_sub(&tree, p.clone(), &tr, ty_inner)),
                    ty: Box::new(TypeT::Base),
                },
            );
            tree.insertion(p.clone(), tr);
            args.insertion(p.clone(), args_inner);
        }
    }

    let tyn = tyt.eval(
        &SemCtx::id(tree.get_paths().into_iter().map(|(x, _)| Pos::Path(x))),
        env,
    );

    let (final_ty, susp) = tyn.de_susp(tree.susp_level());

    for _ in 0..susp {
        tree = tree.branches.remove(0);
    }

    if env.reduction.disc_rem
        && tree.is_disc()
        && tree.dim() == 1
        && final_ty
            == TypeN(vec![(
                TermN::Variable(Pos::Path(Path::here(0))),
                TermN::Variable(Pos::Path(Path::here(1))),
            )])
    {
        return args.unwrap_disc();
    }

    if env.reduction.endo_coh
        && final_ty.0.last().is_some_and(|(s, t)| s == t)
        && (tree.dim() != 0
            || final_ty
                != TypeN(vec![(
                    TermN::Variable(Pos::Path(Path::here(0))),
                    TermN::Variable(Pos::Path(Path::here(0))),
                )]))
    {
        let susp = final_ty.dim() - 1;
        if let TypeT::Arr(s, a, _) = final_ty.quote() {
            let sem_ctx = SemCtx::new(
                args.get_paths()
                    .into_iter()
                    .map(|(p, tm)| (Pos::Path(p), tm.clone()))
                    .collect(),
                TypeN(vec![]),
            );

            let args = s.eval(&sem_ctx, env).to_args(a.eval(&sem_ctx, env));

            return TermN::Other(
                HeadN {
                    tree: Tree::singleton(NoDispOption(Some("x".into()))),
                    ty: TypeN(vec![(
                        TermN::Variable(Pos::Path(Path::here(0))),
                        TermN::Variable(Pos::Path(Path::here(0))),
                    )]),
                    susp,
                },
                args,
            );
        }
    }

    TermN::Other(
        HeadN {
            tree,
            ty: final_ty,
            susp,
        },
        args,
    )
}

impl TermT {
    pub fn eval(&self, ctx: &SemCtx, env: &Environment) -> TermN {
        match self {
            TermT::App(t, awt) => t.eval(&awt.eval(ctx, env), env),
            TermT::Var(pos) => ctx.get(pos).clone(),
            TermT::TopLvl(name) => env.top_level.get(name).unwrap().1.eval(ctx, env),
            TermT::Susp(t) => t.eval(&ctx.clone().restrict(), env),
            TermT::Include(t, rng) => t.eval(&ctx.clone().include(rng), env),
            TermT::UComp(tr, ty) => eval_coh(tr.clone(), *ty.clone(), ctx, env),
            TermT::Coh(tr, ty) => eval_coh(tr.clone(), *ty.clone(), ctx, env),
        }
    }
}

impl TypeT {
    pub fn eval(&self, ctx: &SemCtx, env: &Environment) -> TypeN {
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
    pub fn eval(&self, ctx: &SemCtx, env: &Environment) -> SemCtx {
        self.args.eval(&self.ty, ctx, env)
    }
}

impl ArgsT {
    pub fn eval(&self, ty: &TypeT, ctx: &SemCtx, env: &Environment) -> SemCtx {
        match self {
            ArgsT::Sub(ts) => {
                let map = ts
                    .iter()
                    .enumerate()
                    .map(|(i, t)| (Pos::Level(i), t.eval(ctx, env)))
                    .collect();
                let tyn = ty.eval(ctx, env);
                SemCtx::new(map, tyn)
            }
            ArgsT::Label(tr) => {
                let pairs = tr.get_paths();

                let map = pairs
                    .into_iter()
                    .map(|(path, tm)| (Pos::Path(path), tm.eval(ctx, env)))
                    .collect();

                let tyn = ty.eval(ctx, env);
                SemCtx::new(map, tyn)
            }
        }
    }
}

impl HeadN {
    pub fn quote(&self) -> TermT {
        let HeadN { tree, ty, susp } = self;
        let mut x = TermT::Coh(tree.clone(), Box::new(ty.quote()));
        for _ in 0..*susp {
            x = TermT::Susp(Box::new(x));
        }
        x
    }
}

impl TermN {
    pub fn quote(&self) -> TermT {
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

impl TypeN {
    pub fn quote(&self) -> TypeT {
        let mut ret = TypeT::Base;

        for (s, t) in &self.0 {
            ret = TypeT::Arr(s.quote(), Box::new(ret), t.quote())
        }

        ret
    }
}

impl LabelT {
    pub fn exterior_sub<T>(
        outer: &Tree<T>,
        mut bp: Path,
        inner: &Tree<NoDispOption<Name>>,
        ty: TypeN,
    ) -> LabelT {
        match bp.path.pop() {
            Some(i) => {
                let mut l = outer.path_tree().map(&|p| TermT::Var(Pos::Path(p)));

                l.branches[i] = LabelT::exterior_sub(&outer.branches[i], bp, inner, ty)
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

                let inner_args = TermN::Other(
                    HeadN {
                        tree: inner.clone(),
                        ty: ty.clone(),
                        susp: 0,
                    },
                    inner.path_tree().map(&|p| TermN::Variable(Pos::Path(p))),
                )
                .to_args(ty)
                .map(&|tm| TermT::Include(Box::new(tm.quote()), bp.here..=bp.here + inner_size));
                l.branches.splice(bp.here..bp.here + 1, inner_args.branches);

                l
            }
        }
    }
}
