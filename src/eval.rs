use std::collections::HashMap;

use crate::{
    common::{Path, Pos, Tree},
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

    pub fn id(positions: impl Iterator<Item = Pos>, susp: usize) -> Self {
        SemCtx::new(
            positions
                .map(|pos| (pos.clone(), TermN::Variable(pos.susp(susp))))
                .collect(),
            TypeN::Base,
        )
    }

    pub fn get(&self, pos: &Pos) -> TermN {
        self.map.get(&pos).unwrap().clone()
    }

    pub fn get_ty(&self) -> TypeN {
        self.ty.clone()
    }

    pub fn restrict(mut self) -> Self {
        let ty = TypeN::Arr(
            self.map
                .remove(&Pos::Path(Path::here(0)))
                .or(self.map.remove(&Pos::Level(0)))
                .unwrap(),
            Box::new(self.ty),
            self.map
                .remove(&Pos::Path(Path::here(1)))
                .or(self.map.remove(&Pos::Level(1)))
                .unwrap(),
        );

        let map = self
            .map
            .into_iter()
            .map(|(pos, tm)| (pos.de_susp(), tm))
            .collect();

        SemCtx { ty, map }
    }
}

impl Tree<TermN> {
    pub fn unrestrict(self, ty: TypeN) -> Self {
        match ty {
            TypeN::Base => self,
            TypeN::Arr(s, a, t) => {
                let new_tree = Tree {
                    elements: vec![s, t],
                    branches: vec![self],
                };

                new_tree.unrestrict(*a)
            }
        }
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

                let new_ctx =
                    SemCtx::id(tr.get_paths().into_iter().map(|(p, _)| Pos::Path(p)), dim);
                let mut tree = tr.clone();
                for _ in 0..dim {
                    tree = tree.susp();
                }

                let args = tr.from_paths(
                    &mut tr
                        .get_paths()
                        .into_iter()
                        .map(|(p, _)| ctx.get(&Pos::Path(p)).clone()),
                );

                let final_ty = ty.eval(&new_ctx, env);

                TermN::Other(
                    HeadN::Coh(tree, Box::new(final_ty)),
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
            TypeT::Arr(s, a, t) => TypeN::Arr(
                s.eval(ctx, env),
                Box::new(a.eval(ctx, env)),
                t.eval(ctx, env),
            ),
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
            HeadN::Coh(tr, ty) => TermT::Coh(tr.clone(), Box::new(ty.quote())),
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
                    args: ArgsT::Label(args.map(&|tm| tm.quote())),
                    ty: Box::new(TypeT::Base),
                },
            ),
        }
    }
}

impl TypeN {
    pub fn quote(&self) -> TypeT {
        match self {
            TypeN::Base => TypeT::Base,
            TypeN::Arr(s, a, t) => TypeT::Arr(s.quote(), Box::new(a.quote()), t.quote()),
        }
    }
}
