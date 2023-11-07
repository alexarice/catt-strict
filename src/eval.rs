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

    pub fn id(positions: impl Iterator<Item = Pos>) -> Self {
        SemCtx::new(
            positions
                .map(|pos| (pos.clone(), TermN::Variable(pos)))
                .collect(),
            TypeN::base(),
        )
    }

    pub fn get(&self, pos: &Pos) -> TermN {
        self.map.get(&pos).unwrap().clone()
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

                let new_ctx = SemCtx::id(tr.get_paths().into_iter().map(|(p, _)| Pos::Path(p)));
                let tree = tr.clone();

                let args = tr.path_tree().map(&|p| ctx.get(&Pos::Path(p)));

                let final_ty = ty.eval(&new_ctx, env);

                TermN::Other(
                    HeadN {
                        tree,
                        ty: final_ty,
                        susp: dim,
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
