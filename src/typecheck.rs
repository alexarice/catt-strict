use std::collections::HashMap;

use thiserror::Error;

use crate::{
    common::{Name, NoDispOption, Pos, Tree},
    eval::SemCtx,
    normal::{TermN, TypeN},
    syntax::{Args, Ctx, Label, Sub, Term, Type},
    term::{ArgsT, ArgsWithTypeT, CtxT, LabelT, TermT, TypeT},
};

pub struct Local {
    pub ctx: CtxT,
    pub map: HashMap<Name, (Pos, TypeT)>,
}

impl Tree<NoDispOption<Name>> {
    pub fn to_map(&self) -> Local {
        let pairs = self.get_paths();
        let map = pairs
            .into_iter()
            .filter_map(|(path, mname)| {
                mname.0.clone().map(|name| {
                    let ty = path.to_type();
                    (name, (Pos::Path(path), ty))
                })
            })
            .collect();

        Local {
            ctx: CtxT::Tree(self.clone()),
            map,
        }
    }
}

pub enum Insertion {
    Pruning,
    Full,
}

pub struct Reduction {
    pub disc_rem: bool,
    pub endo_coh: bool,
    pub insertion: Option<Insertion>,
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
    #[error("Cannot infer context for {0}")]
    CannotInferCtx(Term),
    #[error("Checking inferable term {0} is unsupported")]
    CannotCheck(Term),
    #[error("Type checking {0} is unsupported")]
    UnsupportedCheck(Type),
    #[error("Support check failed for type {0:?}")]
    SupportCheck(TypeT),
}

impl Term {
    pub fn infer(&self, env: &Environment) -> Result<(CtxT, TermT, TypeT), TypeCheckError> {
        match self {
            Term::Susp(t) => {
                let (ctx, tm, ty) = t.infer(env)?;
                Ok((
                    ctx.susp(),
                    TermT::Susp(Box::new(tm)),
                    TypeT::Susp(Box::new(ty)),
                ))
            }
            Term::Var(x) => env
                .top_level
                .get(x)
                .cloned()
                .map(|(ctx, _, ty)| (ctx, TermT::TopLvl(x.clone()), ty))
                .ok_or(TypeCheckError::UnknownTopLevel(x.clone())),
            Term::Coh(tr, ty) => {
                let (tyt, tyn) = ty.infer(env, &tr.to_map())?;

		if ! tyn.support_check(tr, &env.support) {
		    return Err(TypeCheckError::SupportCheck(tyt))
		}

                Ok((
                    CtxT::Tree(tr.clone()),
                    TermT::Coh(tr.clone(), Box::new(tyt.clone())),
                    tyt,
                ))
            }
            t => Err(TypeCheckError::CannotInferCtx(t.clone())),
        }
    }

    pub fn check(
        &self,
        env: &Environment,
        local: &Local,
    ) -> Result<(TermT, TypeT), TypeCheckError> {
        match self {
            Term::Var(x) => local
                .map
                .get(x)
                .map(|(p, ty)| (TermT::Var(p.clone()), ty.clone()))
                .ok_or(TypeCheckError::UnknownVariable(x.clone())),
            Term::App(head, args) => {
                let (ctx, tm, ty) = head.infer(env)?;
                let awt = args.args.infer(env, local, &ctx)?;
                if let Some(t) = &args.ty {
                    t.check(env, local, &awt.ty.eval(&SemCtx::id(ctx.positions()), env))?;
                }

                Ok((
                    TermT::App(Box::new(tm), awt.clone()),
                    TypeT::App(Box::new(ty), awt),
                ))
            }
            t => Err(TypeCheckError::CannotCheck(t.clone())),
        }
    }
}

impl Type {
    pub fn infer(&self, env: &Environment, local: &Local) -> Result<(TypeT, TypeN), TypeCheckError> {
        match self {
            Type::Base => Ok((TypeT::Base, TypeN(vec![]))),
            Type::Arr(s, a, t) => {
                let (st, ty1) = s.check(env, local)?;
                let (tt, ty2) = t.check(env, local)?;
                let sem_ctx = SemCtx::id(local.ctx.positions());
		let sn = st.eval(&sem_ctx, env);
                let ty1n = ty1.eval(&sem_ctx, env);
		let tn = tt.eval(&sem_ctx, env);
                let ty2n = ty2.eval(&sem_ctx, env);
                if ty1n != ty2n {
                    return Err(TypeCheckError::TypeMismatch(ty1n, ty2n));
                }
                let (tyt, mut tyn) = if let Some(ty) = a {
                    let (tyt, tyn) = ty.infer(env, local)?;
		    if tyn != ty1n {
			return Err(TypeCheckError::TypeMismatch(tyn, ty1n));
		    }
		    (tyt, tyn)
                } else {
		    (ty1n.quote(), ty1n)
		};

		tyn.0.push((sn, tn));
		Ok((TypeT::Arr(st, Box::new(tyt), tt), tyn))
            }
            ty => Err(TypeCheckError::UnsupportedCheck(ty.clone())),
        }
    }

    pub fn check(
        &self,
        env: &Environment,
        local: &Local,
        ty: &TypeN,
    ) -> Result<(), TypeCheckError> {
        let (_, tyn) = self.infer(env, local)?;
	if &tyn != ty {
	    return Err(TypeCheckError::TypeMismatch(tyn, ty.clone()));
	}
	Ok(())
    }
}

impl Label {
    pub fn from_sub<T>(sub: &Sub, tree: &Tree<T>) -> Result<Self, TypeCheckError> {
        let mut iter = sub.iter().cloned();
        tree.label_from_max(&mut iter)
            .ok_or(TypeCheckError::LabelSub)
    }

    pub fn infer(
        &self,
        env: &Environment,
        local: &Local,
    ) -> Result<(LabelT, TypeN), TypeCheckError> {
        if self.branches.is_empty() {
            let (tm, ty) = self
                .elements
                .first()
                .unwrap()
                .0
                .as_ref()
                .ok_or(TypeCheckError::LocMaxMissing)?
                .check(env, local)?;
            return Ok((
                Tree::singleton(tm),
                ty.eval(&SemCtx::id(local.ctx.positions()), env),
            ));
        }
        let mut branches = vec![];
        let mut el_norm = vec![];
        let mut ty = None;
        for br in &self.branches {
            let (l, mut ty1) = br.infer(env, local)?;
            branches.push(l);

            let (s, t) = ty1.0.pop().ok_or(TypeCheckError::DimensionMismatch)?;
            if let Some(s1) = el_norm.last() {
                if &s != s1 {
                    return Err(TypeCheckError::TermMismatch(s, s1.clone()));
                }
            } else {
                el_norm.push(s);
            }
            el_norm.push(t);
            ty.get_or_insert(ty1);
        }

        let elements = self
            .elements
            .iter()
            .zip(el_norm)
            .map(|(el, eln)| match &el.0 {
                Some(tm) => {
                    let tmt = tm.check(env, local)?.0;
                    let tmn = tmt.eval(&SemCtx::id(local.ctx.positions()), env);
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
        local: &Local,
        ctxt: &CtxT,
    ) -> Result<ArgsWithTypeT, TypeCheckError> {
        match (ctxt, self) {
            (CtxT::Ctx(ctx), Args::Sub(sub)) => {
                let (args, tys): (Vec<TermT>, Vec<TypeT>) = sub
                    .iter()
                    .map(|t| t.check(env, local))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .unzip();
                let awt = ArgsWithTypeT {
                    args: ArgsT::Sub(args),
                    ty: Box::new(tys[0].clone()),
                };

                let sem_ctx = SemCtx::id(ctxt.positions());

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
    pub fn check(&self, env: &Environment) -> Result<Local, TypeCheckError> {
        match self {
            Ctx::Tree(tr) => Ok(tr.to_map()),
            Ctx::Other(ctx) => {
                let mut local = Local {
                    ctx: CtxT::Ctx(vec![]),
                    map: HashMap::new(),
                };
                for (level, (name, ty)) in ctx.iter().enumerate() {
                    let (tyt, _) = ty.infer(env, &local)?;
                    if let CtxT::Ctx(ctxt) = &mut local.ctx {
                        ctxt.push((Some(name.clone()), tyt.clone()));
                    }
                    local.map.insert(name.clone(), (Pos::Level(level), tyt));
                }

                Ok(local)
            }
        }
    }
}
