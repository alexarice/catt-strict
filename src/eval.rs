use std::collections::HashMap;

use crate::{
    common::{NoDispOption, Path, Pos, Tree},
    normal::{HeadN, TermN, TypeN},
    term::{ArgsT, ArgsWithTypeT, TermT, TypeT},
    typecheck::Environment,
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

    pub fn id() -> Self {
        SemCtx::new(HashMap::new(), TypeN::base())
    }

    pub fn get(&self, pos: &Pos) -> TermN {
        self.map
            .get(&pos)
            .cloned()
            .unwrap_or(TermN::Variable(pos.clone()))
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
}

impl TermT {
    pub fn eval(&self, ctx: &SemCtx, env: &Environment) -> TermN {
        match &self {
            TermT::App(t, awt) => t.eval(&awt.eval(ctx, env), env),
            TermT::Var(pos) => ctx.get(pos).clone(),
            TermT::TopLvl(name) => env.top_level.get(name).unwrap().1.eval(ctx, env),
            TermT::Susp(t) => t.eval(&ctx.clone().restrict(), env),
            TermT::Coh(tr, ty) => {
                let sem_ty = ctx.get_ty();
                let dim = sem_ty.dim();

                let new_ctx = SemCtx::id();

                let tyn = ty.eval(&new_ctx, env);

                let (final_ty, ty_susp) = tyn.de_susp(tr.susp_level());

                let mut tree = tr.clone();
                for _ in 0..ty_susp {
                    tree = tree.branches.remove(0);
                }

                if env.reduction.disc_rem {
                    if tree.is_disc()
                        && tree.dim() == 1
                        && final_ty
                            == TypeN(vec![(
                                TermN::Variable(Pos::Path(Path::here(0))),
                                TermN::Variable(Pos::Path(Path::here(1))),
                            )])
                    {
                        return ctx.get(&Pos::Path(tr.get_maximal_paths().remove(0)));
                    }
                }

                if env.reduction.endo_coh {
                    if final_ty.0.last().is_some_and(|(s, t)| s == t) {
                        if tree.dim() != 0
                            || final_ty
                                != TypeN(vec![(
                                    TermN::Variable(Pos::Path(Path::here(0))),
                                    TermN::Variable(Pos::Path(Path::here(0))),
                                )])
                        {
                            // Not already an identity

                            match final_ty.quote() {
                                TypeT::Arr(s, a, _) => {
                                    let new_args_with_ty = ArgsWithTypeT {
                                        args: ArgsT::Label(Tree::singleton(s)),
                                        ty: a,
                                    };
                                    let tmt = TermT::App(
                                        Box::new(TermT::Coh(
                                            Tree::singleton(NoDispOption(None)),
                                            Box::new(TypeT::Arr(
                                                TermT::Var(Pos::Path(Path::here(0))),
                                                Box::new(TypeT::Base),
                                                TermT::Var(Pos::Path(Path::here(0))),
                                            )),
                                        )),
                                        new_args_with_ty,
                                    );

                                    return tmt.eval(ctx, env);
                                }
                                _ => unreachable!(),
                            }
                        }
                    }
                }

                let args = tr.path_tree().map(&|p| ctx.get(&Pos::Path(p)));

                TermN::Other(
                    HeadN {
                        tree,
                        ty: final_ty,
                        susp: dim + ty_susp,
                    },
                    args.unrestrict(sem_ty),
                )
            }
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
        match self {
            HeadN { tree, ty, susp } => {
                let mut x = TermT::Coh(tree.clone(), Box::new(ty.quote()));
                for _ in 0..*susp {
                    x = TermT::Susp(Box::new(x));
                }
                x
            }
        }
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
