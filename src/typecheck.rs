use std::collections::HashMap;

use thiserror::Error;

use crate::{
    common::{Name, NoDispOption, Pos, Tree},
    eval::SemCtx,
    normal::{TermN, TypeN},
    syntax::{Args, Ctx, Head, Label, Sub, Term, Type},
    term::{ArgsT, ArgsWithTypeT, CtxT, LabelT, TermT, TypeT},
};

impl Tree<NoDispOption<Name>> {
    pub fn to_map(&self) -> HashMap<Name, (Pos, TypeT)> {
        let pairs = self.get_paths();
        pairs
            .into_iter()
            .filter_map(|(path, mname)| {
                mname.0.clone().map(|name| {
                    let ty = path.to_type();
                    (name, (Pos::Path(path), ty))
                })
            })
            .collect()
    }
}

pub enum Reduction {
    None,
    // SU,
    // SUA,
}

pub enum Support {
    FullInverse,
    NoInverse,
}

pub struct Environment {
    pub top_level: HashMap<Name, (CtxT, TermT, TypeT)>,
    pub reduction: Reduction,
    pub support: Support,
}

impl SemCtx {
    pub fn from_map(local: &HashMap<Name, (Pos, TypeT)>) -> Self {
        SemCtx::id(local.values().map(|(pos, _)| pos.clone()), 0)
    }
}

#[derive(Error, Debug)]
pub enum TypeCheckError {
    #[error("Unknown variable {0}")]
    UnknownVariable(Name),
    #[error("Unknown top level symbol {0}")]
    UnknownTopLevel(Name),
    #[error("Labelling found where substitution expected")]
    LabelSub,
    #[error("Type mismatch:, expected {0:?}, found {1:?}")]
    TypeMismatch(TypeN, TypeN),
    #[error("Term mismatch:, expected {0:?}, found {1:?}")]
    TermMismatch(TermN, TermN),
    #[error("Dimension mismatch")]
    DimensionMismatch,
    #[error("Missing locally maximal variable")]
    LocMaxMissing,
    #[error("Empty substitution")]
    EmptySub,
}

impl Term {
    pub fn infer(
        &self,
        env: &Environment,
        local: &HashMap<Name, (Pos, TypeT)>,
    ) -> Result<(TermT, TypeT), TypeCheckError> {
        match &self {
            Term::Var(x) => local
                .get(x)
                .map(|(p, ty)| (TermT::Var(p.clone()), ty.clone()))
                .ok_or(TypeCheckError::UnknownVariable(x.clone())),
            Term::WithArgs(head, args, aty) => {
                let (ctx, tm, ty) = head.infer(&env)?;

                let awt = args.infer(env, local, &ctx)?;

                if let Some(t) = aty {
                    t.check(env, local, &awt.ty.eval(&SemCtx::from_map(local), env))?;
                }

                Ok((
                    TermT::App(Box::new(tm), awt.clone()),
                    TypeT::App(Box::new(ty), awt),
                ))
            }
        }
    }
}

impl Head {
    pub fn infer(&self, env: &Environment) -> Result<(CtxT, TermT, TypeT), TypeCheckError> {
        match &self {
            Head::Susp(t) => {
                let (ctx, tm, ty) = t.infer(env)?;
                Ok((
                    ctx.susp(),
                    TermT::Susp(Box::new(tm)),
                    TypeT::Susp(Box::new(ty)),
                ))
            }
            Head::TopLvl(x) => env
                .top_level
                .get(x)
                .cloned()
                .map(|(ctx, _, ty)| (ctx, TermT::TopLvl(x.clone()), ty))
                .ok_or(TypeCheckError::UnknownTopLevel(x.clone())),
            Head::Coh(tr, ty) => {
                let tyt = ty.infer(&env, &tr.to_map())?;

                // TODO: Support check

                Ok((
                    CtxT::Tree(tr.clone()),
                    TermT::Coh(tr.clone(), Box::new(tyt.clone())),
                    tyt,
                ))
            }
        }
    }
}

impl Type {
    pub fn infer(
        &self,
        env: &Environment,
        local: &HashMap<Name, (Pos, TypeT)>,
    ) -> Result<TypeT, TypeCheckError> {
        match self {
            Type::Base => Ok(TypeT::Base),
            Type::Arr(s, a, t) => {
                let (st, ty1) = s.infer(env, local)?;
                let (tt, ty2) = t.infer(env, local)?;
                let sem_ctx = SemCtx::from_map(local);
                let ty1n = ty1.eval(&sem_ctx, env);
                let ty2n = ty2.eval(&sem_ctx, env);
                if ty1n != ty2n {
                    return Err(TypeCheckError::TypeMismatch(ty1n, ty2n));
                }
                if let Some(ty) = a {
                    ty.check(env, local, &ty1n)?;
                }
                Ok(TypeT::Arr(st, Box::new(ty1n.quote()), tt))
            }
        }
    }

    pub fn check(
        &self,
        env: &Environment,
        local: &HashMap<Name, (Pos, TypeT)>,
        ty: &TypeN,
    ) -> Result<(), TypeCheckError> {
        match (self, ty) {
            (Type::Base, TypeN::Base) => Ok(()),
            (Type::Base, TypeN::Arr(_, _, _)) => Err(TypeCheckError::DimensionMismatch),
            (Type::Arr(_, _, _), TypeN::Base) => Err(TypeCheckError::DimensionMismatch),
            (Type::Arr(s1, ty1, t1), TypeN::Arr(s2, ty2, t2)) => {
                let sem_ctx = SemCtx::from_map(local);
                let (s1t, _) = s1.infer(env, local)?;
                let s1n = s1t.eval(&sem_ctx, env);
                if &s1n != s2 {
                    return Err(TypeCheckError::TermMismatch(s1n, s2.clone()));
                }
                let (t1t, _) = t1.infer(env, local)?;
                let t1n = t1t.eval(&sem_ctx, env);
                if &t1n != t2 {
                    return Err(TypeCheckError::TermMismatch(t1n, t2.clone()));
                }
                if let Some(ty) = ty1 {
                    ty.check(env, local, ty2)?;
                }
                Ok(())
            }
        }
    }
}

impl Label {
    pub fn from_sub<T>(sub: &Sub, tree: &Tree<T>) -> Result<Self, TypeCheckError> {
        let mut iter = sub.iter();
        tree.label_from_max(&mut iter)
            .ok_or(TypeCheckError::LabelSub)
    }

    pub fn infer(
        &self,
        env: &Environment,
        local: &HashMap<Name, (Pos, TypeT)>,
    ) -> Result<(LabelT, TypeN), TypeCheckError> {
        if self.branches.is_empty() {
            let (tm, ty) = self
                .elements
                .first()
                .unwrap()
                .0
                .as_ref()
                .ok_or(TypeCheckError::LocMaxMissing)?
                .infer(env, local)?;
            return Ok((Tree::singleton(tm), ty.eval(&SemCtx::from_map(local), env)));
        }

        let mut branches = vec![];
        let mut el_norm = vec![];
        let mut ty = None;
        for br in &self.branches {
            let (l, ty1) = br.infer(env, local)?;
            branches.push(l);
            match ty1 {
                TypeN::Base => return Err(TypeCheckError::DimensionMismatch),
                TypeN::Arr(s, a, t) => {
                    if let Some(s1) = el_norm.last() {
                        if &s != s1 {
                            return Err(TypeCheckError::TermMismatch(s, s1.clone()));
                        }
                    } else {
                        el_norm.push(s);
                    }
                    el_norm.push(t);
                    ty.get_or_insert(*a);
                }
            }
        }

        let elements = self
            .elements
            .iter()
            .zip(el_norm)
            .map(|(el, eln)| match &el.0 {
                Some(tm) => {
                    let tmt = tm.infer(env, local)?.0;
                    let tmn = tmt.eval(&SemCtx::from_map(local), env);
                    if tmn != eln {
                        Err(TypeCheckError::TermMismatch(tmn, eln))
                    } else {
                        Ok(tmt)
                    }
                }
                None => Ok(eln.quote()),
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok((Tree { elements, branches }, ty.unwrap()))
    }
}

impl Args {
    pub fn infer(
        &self,
        env: &Environment,
        local: &HashMap<Name, (Pos, TypeT)>,
        ctx: &CtxT,
    ) -> Result<ArgsWithTypeT, TypeCheckError> {
        match (ctx, self) {
            (CtxT::Ctx(ctx), Args::Sub(sub)) => {
                let (args, tys): (Vec<TermT>, Vec<TypeT>) = sub
                    .iter()
                    .map(|t| t.infer(env, local))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .unzip();
                let awt = ArgsWithTypeT {
                    args: ArgsT::Sub(args),
                    ty: Box::new(tys[0].clone()),
                };

                let sem_ctx = SemCtx::from_map(local);

                let args_sem_ctx = awt.eval(&sem_ctx, env);

                for (x, y) in ctx.iter().map(|x| &x.1).zip(tys) {
                    let xn = x.eval(&args_sem_ctx, env);
                    let yn = y.eval(&sem_ctx, env);
                    if xn != yn {
                        return Err(TypeCheckError::TypeMismatch(xn, yn));
                    }
                }

                Ok(awt)
            }
            (CtxT::Ctx(_), Args::Label(_)) => Err(TypeCheckError::LabelSub),
            (CtxT::Tree(ctx), Args::Sub(sub)) => Label::from_sub(sub, ctx).and_then(|l| {
                l.infer(env, local).map(|(lt, ty)| ArgsWithTypeT {
                    args: ArgsT::Label(lt),
                    ty: Box::new(ty.quote()),
                })
            }),
            (CtxT::Tree(_), Args::Label(l)) => l.infer(env, local).map(|(lt, ty)| ArgsWithTypeT {
                args: ArgsT::Label(lt),
                ty: Box::new(ty.quote()),
            }),
        }
    }
}

impl Ctx {
    pub fn check(
        &self,
        env: &Environment,
    ) -> Result<(CtxT, HashMap<Name, (Pos, TypeT)>), TypeCheckError> {
        match self {
            Ctx::Tree(tr) => Ok((CtxT::Tree(tr.clone()), tr.to_map())),
            Ctx::Other(ctx) => {
                let mut level = 0;
                let mut ctxt = vec![];
                let mut local = HashMap::new();
                for (name, ty) in ctx {
                    let tyt = ty.infer(&env, &local)?;
                    ctxt.push((Some(name.clone()), tyt.clone()));
                    local.insert(name.clone(), (Pos::Level(level), tyt));
                    level += 1;
                }

                Ok((CtxT::Ctx(ctxt), local))
            }
        }
    }
}