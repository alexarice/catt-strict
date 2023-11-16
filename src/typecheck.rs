use std::fmt::Debug;
use std::hash::Hash;
use std::{collections::HashMap, ops::Range};

use ariadne::{Report, ReportKind, Span};
use thiserror::Error;

use crate::{
    common::{Name, NoDispOption, Pos, Spanned, Tree},
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

#[derive(Error, Debug)]
pub enum TypeCheckError<S> {
    #[error("Unknown top level name: {0}")]
    UnknownTopLevel(Name, S),
    #[error("Unknown local variable: {0}")]
    UnknownLocal(Name, S),
    #[error("Type \"{0}\" does not satisfy fullness condition")]
    Fullness(Type<S>),
    #[error("Cannot infer context for term \"{0}\"")]
    CannotInferCtx(Term<S>),
    #[error("Cannot check context for inferrable term \"{0}\"")]
    CannotCheckCtx(Term<S>),
    #[error("Type {0} is not checkable")]
    CannotCheck(Type<S>),
    #[error("Terms did not have matching types")]
    InferredTypesNotEqual(Term<S>, Type<()>, Term<S>, Type<()>, S),
    #[error("Term \"{0}\" had inferred type \"{1}\" but should have type \"{2}\"")]
    InferredTypeWrong(Term<S>, Type<()>, Type<S>),
    #[error("Term \"{0}\" had inferred type \"{1}\" but should have type \"{2}\"")]
    InferredTypeWrongCalc(Term<S>, Type<()>, Type<()>),
    #[error("Given type \"{0}\" does not match inferred type \"{1}\"")]
    TypeMismatch(Type<S>, Type<()>),
    #[error("Given term \"{0}\" does not match inferred term \"{1}\"")]
    TermMismatch(Term<S>, Term<()>),
    #[error("Mismatch between inferred terms \"{1}\" and \"{2}\" in labelling \"{0}\"")]
    LabelMismatch(Label<S>, Term<()>, Term<()>, S),
    #[error("Dimension mismatch in labeling \"{0}\"")]
    DimensionMismatch(Label<S>, S),
    #[error("Substitution \"{0}\" cannot be coerced to labelling")]
    SubToLabel(Args<S>, S),
    #[error("Cannot convert labelling \"{0}\" to substitution")]
    LabelToSub(Label<S>, S),
    #[error("Locally maximal argument missing from labelling ")]
    LocallyMaxMissing(Label<S>, S),
}

impl TypeCheckError<Range<usize>> {
    fn span(&self) -> &Range<usize> {
        match self {
            TypeCheckError::UnknownTopLevel(_, s)
            | TypeCheckError::UnknownLocal(_, s)
            | TypeCheckError::SubToLabel(_, s)
            | TypeCheckError::InferredTypesNotEqual(_, _, _, _, s)
            | TypeCheckError::LabelMismatch(_, _, _, s)
            | TypeCheckError::DimensionMismatch(_, s)
            | TypeCheckError::LabelToSub(_, s)
            | TypeCheckError::LocallyMaxMissing(_, s) => s,
            TypeCheckError::Fullness(ty)
            | TypeCheckError::TypeMismatch(ty, _)
            | TypeCheckError::CannotCheck(ty) => ty.span(),
            TypeCheckError::CannotInferCtx(tm)
            | TypeCheckError::CannotCheckCtx(tm)
            | TypeCheckError::InferredTypeWrong(tm, _, _)
            | TypeCheckError::InferredTypeWrongCalc(tm, _, _)
            | TypeCheckError::TermMismatch(tm, _) => tm.span(),
        }
    }
    pub fn to_report<Id: Debug + Hash + PartialEq + Eq + Clone + Copy>(
        self,
        src: Id,
    ) -> Report<'static, (Id, Range<usize>)> {
        let mut report = Report::build(ReportKind::Error, src, self.span().start())
            .with_message(self.to_string());

        match self {
            TypeCheckError::UnknownTopLevel(_, sp) => report
                .add_label(ariadne::Label::new((src, sp)).with_message("Unknown top level symbol")),
            TypeCheckError::UnknownLocal(_, sp) => report
                .add_label(ariadne::Label::new((src, sp)).with_message("Unknown local variable")),
            TypeCheckError::Fullness(ty) => report.add_label(
                ariadne::Label::new((src, ty.span().clone())).with_message("Type is not full"),
            ),
            TypeCheckError::CannotInferCtx(tm) => report.add_label(
                ariadne::Label::new((src, tm.span().clone()))
                    .with_message("Context cannot be inferred"),
            ),
            TypeCheckError::CannotCheckCtx(tm) => report.add_label(
                ariadne::Label::new((src, tm.span().clone()))
                    .with_message("Context cannot be checked"),
            ),
            TypeCheckError::CannotCheck(ty) => report.add_label(
                ariadne::Label::new((src, ty.span().clone())).with_message("Type is not checkable"),
            ),
            TypeCheckError::InferredTypesNotEqual(tm1, ty1, tm2, ty2, _) => {
                report.add_label(
                    ariadne::Label::new((src, tm2.span().clone()))
                        .with_message(format!("Has type {ty2}"))
                        .with_order(0),
                );
                report.add_label(
                    ariadne::Label::new((src, tm1.span().clone()))
                        .with_message(format!("Has type {ty1}"))
                        .with_order(1),
                );
                report.set_note("Terms in an arrow type should have equal type");
            }
            TypeCheckError::InferredTypeWrong(tm, ity, gty) => {
                report.add_label(
                    ariadne::Label::new((src, tm.span().clone()))
                        .with_message(format!("Term has inferred type {ity}")),
                );
                report.add_label(
                    ariadne::Label::new((src, gty.span().clone()))
                        .with_message(format!("Term should have type {gty}")),
                );
            }
            TypeCheckError::InferredTypeWrongCalc(tm, ity, gty) => {
                report.add_label(ariadne::Label::new((src, tm.span().clone())).with_message(
                    format!("Term has inferref type {ity} but should have type {gty}"),
                ));
            }
            TypeCheckError::TypeMismatch(ty, _) => {
                report.add_label(
                    ariadne::Label::new((src, ty.span().clone())).with_message("Given type"),
                );
            }
            TypeCheckError::TermMismatch(tm, _) => {
                report.add_label(
                    ariadne::Label::new((src, tm.span().clone())).with_message("Given term"),
                );
            }
            TypeCheckError::LabelMismatch(_, _, _, sp) => {
                report.add_label(
                    ariadne::Label::new((src, sp.clone()))
                        .with_message("Term mismatch in labelling"),
                );
            }
            TypeCheckError::DimensionMismatch(_, sp) => {
                report.add_label(
                    ariadne::Label::new((src, sp.clone()))
                        .with_message("Dimension mismatch in labelling"),
                );
            }
            TypeCheckError::SubToLabel(_, sp) => {
                report.add_label(
                    ariadne::Label::new((src, sp.clone()))
                        .with_message("Substitution cannot be coerced"),
                );
            }
            TypeCheckError::LabelToSub(_, sp) => {
                report.add_label(
                    ariadne::Label::new((src, sp.clone()))
                        .with_message("Label found when substitution expected"),
                );
            }
            TypeCheckError::LocallyMaxMissing(_, sp) => {
                report.add_label(
                    ariadne::Label::new((src, sp.clone()))
                        .with_message("Locally maximal argument missing"),
                );
            }
        }
        report.finish()
    }
}

impl<S: Clone + Debug> Term<S> {
    pub fn infer(&self, env: &Environment) -> Result<(CtxT, TermT, TypeT), TypeCheckError<S>> {
        match self {
            Term::Susp(t, _) => {
                let (ctx, tm, ty) = t.infer(env)?;
                Ok((
                    ctx.susp(),
                    TermT::Susp(Box::new(tm)),
                    TypeT::Susp(Box::new(ty)),
                ))
            }
            Term::Var(x, sp) => env
                .top_level
                .get(x)
                .cloned()
                .map(|(ctx, _, ty)| (ctx, TermT::TopLvl(x.clone()), ty))
                .ok_or(TypeCheckError::UnknownTopLevel(x.clone(), sp.clone())),
            Term::Coh(tr, ty, _) => {
                let (tyt, tyn) = ty.infer(env, &tr.to_map())?;

                if !tyn.support_check(tr, &env.support) {
                    return Err(TypeCheckError::Fullness(*ty.clone()));
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
    ) -> Result<(TermT, TypeT), TypeCheckError<S>> {
        match self {
            Term::Var(x, sp) => local
                .map
                .get(x)
                .map(|(p, ty)| (TermT::Var(p.clone()), ty.clone()))
                .ok_or(TypeCheckError::UnknownLocal(x.clone(), sp.clone())),
            Term::App(head, args, _) => {
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
            t => Err(TypeCheckError::CannotCheckCtx(t.clone())),
        }
    }
}

impl<S: Clone + Debug> Type<S> {
    pub fn infer(
        &self,
        env: &Environment,
        local: &Local,
    ) -> Result<(TypeT, TypeN), TypeCheckError<S>> {
        match self {
            Type::Base(_) => Ok((TypeT::Base, TypeN(vec![]))),
            Type::Arr(s, a, t, sp) => {
                let (st, ty1) = s.check(env, local)?;
                let (tt, ty2) = t.check(env, local)?;
                let sem_ctx = SemCtx::id(local.ctx.positions());
                let sn = st.eval(&sem_ctx, env);
                let ty1n = ty1.eval(&sem_ctx, env);
                let tn = tt.eval(&sem_ctx, env);
                let ty2n = ty2.eval(&sem_ctx, env);
                let (tyt, mut tyn) = if let Some(ty) = a {
                    let (tyt, tyn) = ty.infer(env, local)?;
                    if tyn != ty1n {
                        let y = ty1n.quote().to_expr(Some(&local.ctx), false);
                        return Err(TypeCheckError::InferredTypeWrong(s.clone(), y, *ty.clone()));
                    }
                    if tyn != ty2n {
                        let y = ty2n.quote().to_expr(Some(&local.ctx), false);
                        return Err(TypeCheckError::InferredTypeWrong(t.clone(), y, *ty.clone()));
                    }
                    (tyt, tyn)
                } else {
                    if ty1n != ty2n {
                        let x = ty1n.quote().to_expr(Some(&local.ctx), false);
                        let y = ty2n.quote().to_expr(Some(&local.ctx), false);
                        return Err(TypeCheckError::InferredTypesNotEqual(
                            s.clone(),
                            x,
                            t.clone(),
                            y,
                            sp.clone(),
                        ));
                    }
                    (ty1n.quote(), ty1n)
                };

                tyn.0.push((sn, tn));
                Ok((TypeT::Arr(st, Box::new(tyt), tt), tyn))
            }
            ty => Err(TypeCheckError::CannotCheck(ty.clone())),
        }
    }

    pub fn check(
        &self,
        env: &Environment,
        local: &Local,
        ty: &TypeN,
    ) -> Result<(), TypeCheckError<S>> {
        let (_, tyn) = self.infer(env, local)?;
        if &tyn != ty {
            let x = ty.quote().to_expr(Some(&local.ctx), false);
            return Err(TypeCheckError::TypeMismatch(self.clone(), x));
        }
        Ok(())
    }
}

impl<S: Clone + Debug> Label<S> {
    fn from_sub<T>(sub: &Sub<S>, tree: &Tree<T>, sp: &S) -> Result<Self, TypeCheckError<S>> {
        let mut iter = sub.iter().cloned();
        tree.label_from_max(&mut iter)
            .map(|tr| tr.map(&|tm| Spanned(tm, sp.clone())))
            .ok_or_else(|| {
                TypeCheckError::SubToLabel(Args::Sub(Spanned(sub.clone(), sp.clone())), sp.clone())
            })
    }

    pub fn infer(
        &self,
        env: &Environment,
        local: &Local,
        sp: &S,
    ) -> Result<(LabelT, TypeN), TypeCheckError<S>> {
        if self.branches.is_empty() {
            let Spanned(tm, sp) = self.elements.first().unwrap();
            let term =
                tm.0.as_ref()
                    .ok_or_else(|| TypeCheckError::LocallyMaxMissing(self.clone(), sp.clone()))?;

            let (tm, ty) = term.check(env, local)?;
            return Ok((
                Tree::singleton(tm),
                ty.eval(&SemCtx::id(local.ctx.positions()), env),
            ));
        }
        let mut branches = vec![];
        let mut el_norm = vec![];
        let mut ty = None;
        for (br, Spanned(_, el_sp)) in self.branches.iter().zip(&self.elements) {
            let (l, mut ty1) = br.infer(env, local, sp)?;
            branches.push(l);

            let (s, t) = ty1
                .0
                .pop()
                .ok_or_else(|| TypeCheckError::DimensionMismatch(self.clone(), sp.clone()))?;
            if let Some(s1) = el_norm.last() {
                if &s != s1 {
                    let x = s.quote().to_expr(Some(&local.ctx), false);
                    let y = s1.quote().to_expr(Some(&local.ctx), false);
                    return Err(TypeCheckError::LabelMismatch(
                        self.clone(),
                        x,
                        y,
                        el_sp.clone(),
                    ));
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
            .map(|(Spanned(el, _), eln)| match &el.0 {
                Some(tm) => {
                    let tmt = tm.check(env, local)?.0;
                    let tmn = tmt.eval(&SemCtx::id(local.ctx.positions()), env);
                    if tmn != eln {
                        let x = eln.quote().to_expr(Some(&local.ctx), false);
                        Err(TypeCheckError::TermMismatch(tm.clone(), x))
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

impl<S: Clone + Debug> Args<S> {
    pub fn infer(
        &self,
        env: &Environment,
        local: &Local,
        ctxt: &CtxT,
    ) -> Result<ArgsWithTypeT, TypeCheckError<S>> {
        match (ctxt, self) {
            (CtxT::Ctx(ctx), Args::Sub(Spanned(sub, _))) => {
                let (args, tys): (Vec<TermT>, Vec<(TypeT, &Term<S>)>) = sub
                    .iter()
                    .map(|t| Ok((t.check(env, local)?, t)))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .map(|((tt, ty), tm)| (tt, (ty, tm)))
                    .unzip();
                let awt = ArgsWithTypeT {
                    args: ArgsT::Sub(args),
                    ty: Box::new(tys[0].0.clone()),
                };

                let sem_ctx = SemCtx::id(local.ctx.positions());

                let args_sem_ctx = awt.eval(&sem_ctx, env);

                for (x, (y, tm)) in ctx.iter().map(|x| &x.1).zip(tys) {
                    let xn = x.eval(&args_sem_ctx, env);
                    let yn = y.eval(&sem_ctx, env);
                    if xn != yn {
                        let xe = x.to_expr(Some(&local.ctx), false);
                        let ye = y.to_expr(Some(&local.ctx), false);
                        return Err(TypeCheckError::InferredTypeWrongCalc(tm.clone(), ye, xe));
                    }
                }

                Ok(awt)
            }
            (CtxT::Ctx(_), Args::Label(Spanned(l, sp))) => {
                Err(TypeCheckError::LabelToSub(l.clone(), sp.clone()))
            }
            (CtxT::Tree(ctx), Args::Sub(Spanned(sub, sp))) => Label::from_sub(sub, ctx, sp)
                .and_then(|l| {
                    l.infer(env, local, sp).map(|(lt, ty)| ArgsWithTypeT {
                        args: ArgsT::Label(lt),
                        ty: Box::new(ty.quote()),
                    })
                }),
            (CtxT::Tree(_), Args::Label(Spanned(l, sp))) => {
                l.infer(env, local, sp).map(|(lt, ty)| ArgsWithTypeT {
                    args: ArgsT::Label(lt),
                    ty: Box::new(ty.quote()),
                })
            }
        }
    }
}

impl<S: Clone + Debug> Ctx<S> {
    pub fn check(&self, env: &Environment) -> Result<Local, TypeCheckError<S>> {
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
