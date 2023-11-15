use std::collections::HashMap;

use eyre::{bail, eyre, Context};

use crate::{
    common::{Name, NoDispOption, Pos, Tree},
    eval::SemCtx,
    normal::TypeN,
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

impl Term {
    pub fn infer(&self, env: &Environment) -> eyre::Result<(CtxT, TermT, TypeT)> {
        self.infer_inner(env)
            .wrap_err_with(|| format!("Cannot infer term {self}"))
    }

    fn infer_inner(&self, env: &Environment) -> eyre::Result<(CtxT, TermT, TypeT)> {
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
                .ok_or(eyre!("Cannot find top level symbol {x}")),
            Term::Coh(tr, ty) => {
                let (tyt, tyn) = ty.infer(env, &tr.to_map())?;

                if !tyn.support_check(tr, &env.support) {
                    bail!("Type {ty} does not satisfy fullness condition");
                }

                Ok((
                    CtxT::Tree(tr.clone()),
                    TermT::Coh(tr.clone(), Box::new(tyt.clone())),
                    tyt,
                ))
            }
            t => Err(eyre!("Cannot infer context for term {t}")),
        }
    }

    pub fn check(&self, env: &Environment, local: &Local) -> eyre::Result<(TermT, TypeT)> {
        self.check_inner(env, local)
            .wrap_err_with(|| format!("Could not check term {self}"))
    }

    fn check_inner(&self, env: &Environment, local: &Local) -> eyre::Result<(TermT, TypeT)> {
        match self {
            Term::Var(x) => local
                .map
                .get(x)
                .map(|(p, ty)| (TermT::Var(p.clone()), ty.clone()))
                .ok_or(eyre!("Unknown local variable {x}")),
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
            t => Err(eyre!("Cannot check context for term {t}")),
        }
    }
}

impl Type {
    pub fn infer(&self, env: &Environment, local: &Local) -> eyre::Result<(TypeT, TypeN)> {
        self.infer_inner(env, local)
            .wrap_err_with(|| format!("Could not infer type {self}"))
    }

    fn infer_inner(&self, env: &Environment, local: &Local) -> eyre::Result<(TypeT, TypeN)> {
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
                    let x = ty1n.quote().to_expr(Some(&local.ctx), false);
                    let y = ty2n.quote().to_expr(Some(&local.ctx), false);
                    bail!("Types {x} and {y} were not equal");
                }
                let (tyt, mut tyn) = if let Some(ty) = a {
                    let (tyt, tyn) = ty.infer(env, local)?;
                    if tyn != ty1n {
                        let y = ty1n.quote().to_expr(Some(&local.ctx), false);
                        bail!("Types {ty} and {y} were not equal");
                    }
                    (tyt, tyn)
                } else {
                    (ty1n.quote(), ty1n)
                };

                tyn.0.push((sn, tn));
                Ok((TypeT::Arr(st, Box::new(tyt), tt), tyn))
            }
            ty => Err(eyre!("Type {ty} cannot be inferred")),
        }
    }

    pub fn check(&self, env: &Environment, local: &Local, ty: &TypeN) -> eyre::Result<()> {
        let (_, tyn) = self.infer(env, local)?;
        if &tyn != ty {
            let x = ty.quote().to_expr(Some(&local.ctx), false);
            bail!("Type {self} does not equal type {x}");
        }
        Ok(())
    }
}

impl Label {
    pub fn from_sub<T>(sub: &Sub, tree: &Tree<T>) -> eyre::Result<Self> {
        let mut iter = sub.iter().cloned();
        tree.label_from_max(&mut iter)
            .ok_or_else(|| eyre!("failed to turn sub {} into tree", Args::Sub(sub.clone())))
    }

    pub fn infer(&self, env: &Environment, local: &Local) -> eyre::Result<(LabelT, TypeN)> {
        self.infer_inner(env, local)
            .wrap_err_with(|| format!("Could not infer labelling {self}"))
    }

    fn infer_inner(&self, env: &Environment, local: &Local) -> eyre::Result<(LabelT, TypeN)> {
        if self.branches.is_empty() {
            let term = self
                .elements
                .first()
                .unwrap()
                .0
                .as_ref()
                .ok_or(eyre!("Locally maximal argument missing"))?;
            let (tm, ty) = term.check(env, local)?;
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

            let (s, t) = ty1.0.pop().ok_or(eyre!("Dimension mismatch of terms"))?;
            if let Some(s1) = el_norm.last() {
                if &s != s1 {
                    let x = s.quote().to_expr(Some(&local.ctx), false);
                    let y = s1.quote().to_expr(Some(&local.ctx), false);
                    bail!("Terms {x} and {y} are not equal");
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
                        let x = eln.quote().to_expr(Some(&local.ctx), false);
                        Err(eyre!("Term {tm} is not equal to inferred term {x}"))
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
    ) -> eyre::Result<ArgsWithTypeT> {
        self.infer_inner(env, local, ctxt)
            .wrap_err_with(|| format!("Cannot infer args {self}"))
    }

    fn infer_inner(
        &self,
        env: &Environment,
        local: &Local,
        ctxt: &CtxT,
    ) -> eyre::Result<ArgsWithTypeT> {
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
                        let xe = x.to_expr(Some(&local.ctx), false);
                        let ye = y.to_expr(Some(&local.ctx), false);
                        bail!("Types {xe} and {ye} are not equal");
                    }
                }

                Ok(awt)
            }
            (CtxT::Ctx(_), Args::Label(_)) => {
                Err(eyre!("Cannot convert labelling to substitution"))
            }
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
    pub fn check(&self, env: &Environment) -> eyre::Result<Local> {
        self.check_inner(env)
            .wrap_err_with(|| format!("Could not check context {self}"))
    }

    fn check_inner(&self, env: &Environment) -> eyre::Result<Local> {
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
