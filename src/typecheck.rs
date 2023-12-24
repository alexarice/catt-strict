use std::fmt::Debug;
use std::hash::Hash;
use std::{collections::HashMap, ops::Range};

use ariadne::{Color, Fmt, Report, ReportKind, Span};
use either::Either;
use thiserror::Error;

use crate::common::{CtxT, Environment, Eval, InferRes, InferResEither, Level, Path, Position};
use crate::normal::TypeNRef;
use crate::term::ArgsT;
use crate::{
    common::{Name, NoDispOption, Spanned, Tree},
    normal::TypeN,
    syntax::{Args, Ctx, Label, Sub, Term, Type},
    term::{ArgsWithTypeT, TermT, TypeT},
};

pub(crate) struct Local<T: Position> {
    pub(crate) ctx: T::Ctx,
    pub(crate) map: HashMap<Name, (T, TypeT<T>)>,
}

impl Tree<NoDispOption<Name>> {
    pub(crate) fn to_map(&self) -> Local<Path> {
        let pairs = self.get_paths();
        let map = pairs
            .into_iter()
            .filter_map(|(path, mname)| {
                mname.0.clone().map(|name| {
                    let ty = path.to_type();
                    (name, (path, ty))
                })
            })
            .collect();

        Local {
            ctx: self.clone(),
            map,
        }
    }
}

#[derive(Error, Debug)]
pub enum TypeCheckError<S> {
    #[error("Unknown top level name: {}", .0.fg(Color::Red))]
    UnknownTopLevel(Name, S),
    #[error("Unknown local variable: {}", .0.fg(Color::Red))]
    UnknownLocal(Name, S),
    #[error("Type \"{}\" does not satisfy fullness condition", .0.fg(Color::Red))]
    Fullness(Type<S>),
    #[error("Cannot infer context for term \"{}\"", .0.fg(Color::Red))]
    CannotInferCtx(Term<S>),
    #[error("Cannot check context for inferrable term \"{}\"", .0.fg(Color::Red))]
    CannotCheckCtx(Term<S>),
    #[error("Identity does not exist in context \"{}\"", .1.fg(Color::Red))]
    IdNotDisc(S, Tree<NoDispOption<Name>>),
    #[error("Type {} is not checkable", .0.fg(Color::Red))]
    CannotCheck(Type<S>),
    #[error("Terms {} and {} do not have matching types", .0.fg(Color::Blue), .2.fg(Color::Magenta))]
    InferredTypesNotEqual(Term<S>, Type<()>, Term<S>, Type<()>, S),
    #[error("Term \"{}\" had inferred type \"{}\" but should have type \"{}\"", .0.fg(Color::Red), .1.fg(Color::Red), .2.fg(Color::Green))]
    InferredTypeWrong(Term<S>, Type<()>, Type<S>),
    #[error("Term \"{}\" had inferred type \"{}\" but should have type \"{}\"", .0.fg(Color::Red), .1.fg(Color::Red), .2.fg(Color::Green))]
    InferredTypeWrongCalc(Term<S>, Type<()>, Type<()>),
    #[error("Given type \"{}\" does not match inferred type \"{}\"", .0.fg(Color::Red), .1.fg(Color::Green))]
    TypeMismatch(Type<S>, Type<()>),
    #[error("Given term \"{}\" does not match inferred term \"{}\"", .0.fg(Color::Red), .1.fg(Color::Green))]
    TermMismatch(Term<S>, Term<()>),
    #[error("Mismatch between inferred terms \"{}\" and \"{}\" in labelling \"{}\"", .1.fg(Color::Magenta), .2.fg(Color::Blue), .0.fg(Color::Red))]
    LabelMismatch(Label<S>, Term<()>, Term<()>, S),
    #[error("Dimension mismatch in labeling \"{}\"", .0.fg(Color::Red))]
    DimensionMismatch(Label<S>, S),
    #[error("Substitution \"{}\" cannot be coerced to labelling", .0.fg(Color::Red))]
    SubToLabel(Args<S>, S),
    #[error("Term \"{}\" should live over tree \"{}\"", .0.fg(Color::Red), .1.fg(Color::Green))]
    TermNotTree(Term<S>, Tree<NoDispOption<Name>>),
    #[error("Locally maximal argument missing from labelling \"{}\"", .0.fg(Color::Red))]
    LocallyMaxMissing(Label<S>, S),
    #[error("Term \"{}\" lives in context \"{}\" but inferred context was \"{}\"", .0.fg(Color::Red), .1.fg(Color::Red), .2.fg(Color::Green))]
    TreeMismatch(Term<S>, Tree<NoDispOption<Name>>, Tree<NoDispOption<Name>>),
    #[error("Cannot check hole")]
    Hole(S),
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
            | TypeCheckError::LocallyMaxMissing(_, s)
            | TypeCheckError::Hole(s)
            | TypeCheckError::IdNotDisc(s, _) => s,
            TypeCheckError::Fullness(ty)
            | TypeCheckError::TypeMismatch(ty, _)
            | TypeCheckError::CannotCheck(ty) => ty.span(),
            TypeCheckError::CannotInferCtx(tm)
            | TypeCheckError::CannotCheckCtx(tm)
            | TypeCheckError::InferredTypeWrong(tm, _, _)
            | TypeCheckError::InferredTypeWrongCalc(tm, _, _)
            | TypeCheckError::TermMismatch(tm, _)
            | TypeCheckError::TreeMismatch(tm, _, _)
            | TypeCheckError::TermNotTree(tm, _) => tm.span(),
        }
    }
    pub(crate) fn into_report<Id>(self, src: &Id) -> Report<'static, (Id, Range<usize>)>
    where
        Id: Debug + Hash + PartialEq + Eq + Clone,
    {
        let mut report = Report::build(ReportKind::Error, src.clone(), self.span().start())
            .with_message(self.to_string());

        match self {
            TypeCheckError::UnknownTopLevel(_, sp) => report.add_label(
                ariadne::Label::new((src.clone(), sp))
                    .with_message("Unknown symbol")
                    .with_color(Color::Red),
            ),
            TypeCheckError::UnknownLocal(_, sp) => report.add_label(
                ariadne::Label::new((src.clone(), sp))
                    .with_message("Unknown variable")
                    .with_color(Color::Red),
            ),
            TypeCheckError::Fullness(ty) => report.add_label(
                ariadne::Label::new((src.clone(), ty.span().clone()))
                    .with_message("Type is not full")
                    .with_color(Color::Red),
            ),
            TypeCheckError::CannotInferCtx(tm) => report.add_label(
                ariadne::Label::new((src.clone(), tm.span().clone()))
                    .with_message("Context cannot be inferred")
                    .with_color(Color::Red),
            ),
            TypeCheckError::CannotCheckCtx(tm) => report.add_label(
                ariadne::Label::new((src.clone(), tm.span().clone()))
                    .with_message("Context cannot be checked")
                    .with_color(Color::Red),
            ),
            TypeCheckError::IdNotDisc(sp, _) => report.add_label(
                ariadne::Label::new((src.clone(), sp))
                    .with_message("id can only occur in disc contexts")
                    .with_color(Color::Red),
            ),
            TypeCheckError::CannotCheck(ty) => report.add_label(
                ariadne::Label::new((src.clone(), ty.span().clone()))
                    .with_message("Type is not checkable")
                    .with_color(Color::Red),
            ),
            TypeCheckError::InferredTypesNotEqual(tm1, ty1, tm2, ty2, _) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), tm2.span().clone()))
                        .with_message(format!("Has type {}", ty2.fg(Color::Magenta)))
                        .with_order(0)
                        .with_color(Color::Magenta),
                );
                report.add_label(
                    ariadne::Label::new((src.clone(), tm1.span().clone()))
                        .with_message(format!("Has type {}", ty1.fg(Color::Blue)))
                        .with_order(1)
                        .with_color(Color::Blue),
                );
                report.set_note("Terms in an arrow type should have equal type");
            }
            TypeCheckError::InferredTypeWrong(tm, ity, gty) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), tm.span().clone()))
                        .with_message(format!("Term has inferred type {}", ity.fg(Color::Red)))
                        .with_color(Color::Red),
                );
                report.add_label(
                    ariadne::Label::new((src.clone(), gty.span().clone()))
                        .with_message(format!("Term should have type {}", gty.fg(Color::Green)))
                        .with_color(Color::Green),
                );
            }
            TypeCheckError::InferredTypeWrongCalc(tm, ity, gty) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), tm.span().clone()))
                        .with_message(format!(
                            "Term has inferred type {} but should have type {}",
                            ity.fg(Color::Red),
                            gty.fg(Color::Green)
                        ))
                        .with_color(Color::Red),
                );
            }
            TypeCheckError::TypeMismatch(ty, _) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), ty.span().clone()))
                        .with_message("Given type")
                        .with_color(Color::Red),
                );
            }
            TypeCheckError::TermMismatch(tm, _) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), tm.span().clone()))
                        .with_message("Given term")
                        .with_color(Color::Red),
                );
            }
            TypeCheckError::LabelMismatch(_, _, _, sp) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), sp))
                        .with_message("Term mismatch in labelling")
                        .with_color(Color::Red),
                );
            }
            TypeCheckError::DimensionMismatch(_, sp) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), sp))
                        .with_message("Dimension mismatch in labelling")
                        .with_color(Color::Red),
                );
            }
            TypeCheckError::SubToLabel(_, sp) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), sp))
                        .with_message("Substitution cannot be coerced")
                        .with_color(Color::Red),
                );
            }
            TypeCheckError::LocallyMaxMissing(_, sp) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), sp))
                        .with_message("Locally maximal argument missing")
                        .with_color(Color::Red),
                );
            }
            TypeCheckError::TermNotTree(t, _) => report.add_label(
                ariadne::Label::new((src.clone(), t.span().clone()))
                    .with_message("Term does not live over tree context")
                    .with_color(Color::Red),
            ),
            TypeCheckError::TreeMismatch(t, _, _) => report.add_label(
                ariadne::Label::new((src.clone(), t.span().clone()))
                    .with_message("Term does not live over correct tree")
                    .with_color(Color::Red),
            ),
            TypeCheckError::Hole(sp) => report.add_label(
                ariadne::Label::new((src.clone(), sp))
                    .with_message("Hole cannot be inferred")
                    .with_color(Color::Red),
            ),
        }
        report.finish()
    }
}

impl<S: Clone + Debug> Term<S> {
    pub(crate) fn infer(&self, env: &Environment) -> Result<InferResEither, TypeCheckError<S>> {
        match self {
            Term::Hole(sp) => Err(TypeCheckError::Hole(sp.clone())),
            Term::Susp(t, _) => {
                let res = t.infer(env)?;
                Ok(res.map_either(InferRes::susp, InferRes::susp))
            }
            Term::Var(x, sp) => env
                .top_level
                .get(x)
                .cloned()
                .map(|res| {
                    res.map_either(
                        |r| InferRes {
                            ctx: r.ctx,
                            tm: TermT::TopLvl(x.clone(), Box::new(r.tm)),
                            ty: r.ty,
                        },
                        |r| InferRes {
                            ctx: r.ctx,
                            tm: TermT::TopLvl(x.clone(), Box::new(r.tm)),
                            ty: r.ty,
                        },
                    )
                })
                .ok_or(TypeCheckError::UnknownTopLevel(x.clone(), sp.clone())),
            Term::Coh(tr, ty, _) => {
                let (tyt, tyn) = ty.infer(env, &tr.to_map())?;

                if !tyn.support_check(tr, &env.support) {
                    return Err(TypeCheckError::Fullness(*ty.clone()));
                }

                Ok(Either::Left(InferRes {
                    ctx: tr.clone(),
                    tm: TermT::Coh(tr.clone(), Box::new(tyt.clone())),
                    ty: tyt,
                }))
            }
            Term::Id(_) => Ok(Either::Left(InferRes {
                ctx: Tree::singleton(NoDispOption(None)),
                tm: TermT::IdT(0),
                ty: TypeT::Arr(
                    TermT::Var(Path::here(0)),
                    Box::new(TypeT::Base),
                    TermT::Var(Path::here(0)),
                ),
            })),
            t => Err(TypeCheckError::CannotInferCtx(t.clone())),
        }
    }

    pub(crate) fn check<T: Eval>(
        &self,
        env: &Environment,
        local: &Local<T>,
    ) -> Result<(TermT<T>, TypeT<T>), TypeCheckError<S>> {
        match self {
            Term::Hole(sp) => Err(TypeCheckError::Hole(sp.clone())),
            Term::Var(x, sp) if local.map.contains_key(x) => local
                .map
                .get(x)
                .map(|(p, ty)| (TermT::Var(p.clone()), ty.clone()))
                .ok_or_else(|| TypeCheckError::UnknownLocal(x.clone(), sp.clone())),
            t @ Term::UComp(_) => local.ctx.check_in_tree(t, |tr| {
                Ok((TermT::UComp(tr.clone()), tr.unbiased_type(tr.dim())))
            }),
            t @ Term::Id(sp) => local.ctx.check_in_tree(t, |tr| {
                if tr.is_disc() {
                    let d = tr.dim();
                    Ok((TermT::IdT(d), tr.unbiased_type(d + 1)))
                } else {
                    Err(TypeCheckError::IdNotDisc(sp.clone(), tr.clone()))
                }
            }),
            Term::App(head, args, _) => match &args.args {
                Args::Sub(Spanned(sub, sp)) => {
                    let res = head.infer(env)?;
                    match res {
                        Either::Left(InferRes { ctx, tm, ty }) => {
                            let label = Label::from_sub(sub, &ctx, sp)?;
                            let (l, lty) = label.infer(env, local, sp)?;

                            if let Some(t) = &args.ty {
                                t.check(env, local, &lty)?;
                            }

                            let awt = ArgsWithTypeT {
                                args: l,
                                ty: Box::new(lty.quote()),
                            };

                            Ok((
                                TermT::AppPath(Box::new(tm), awt.clone()),
                                TypeT::AppPath(Box::new(ty), awt),
                            ))
                        }
                        Either::Right(InferRes { ctx, tm, ty }) => {
                            let (subt, tys): (Vec<TermT<T>>, Vec<_>) = sub
                                .iter()
                                .map(|t| Ok((t.check(env, local)?, t)))
                                .collect::<Result<Vec<_>, _>>()?
                                .into_iter()
                                .map(|((tt, ty), tm)| (tt, (ty, tm)))
                                .unzip();
                            let awt = ArgsWithTypeT {
                                args: subt,
                                ty: Box::new(tys[0].0.clone()),
                            };

                            let sem_ctx = local.ctx.id_sem_ctx();

                            let args_sem_ctx = awt.eval(&sem_ctx, env);

                            for (x, (y, tm)) in ctx.iter().map(|x| &x.1).zip(tys) {
                                let xn = x.eval(&args_sem_ctx, env);
                                let yn = y.eval(&sem_ctx, env);
                                if xn != yn {
                                    let xe = xn.quote().to_expr(Some(&local.ctx), env.implicits);
                                    let ye = yn.quote().to_expr(Some(&local.ctx), env.implicits);
                                    return Err(TypeCheckError::InferredTypeWrongCalc(
                                        tm.clone(),
                                        ye,
                                        xe,
                                    ));
                                }
                            }

                            let tyn = awt.ty.eval(&sem_ctx, env);

                            if let Some(t) = &args.ty {
                                t.check(env, local, &tyn)?;
                            }

                            Ok((
                                TermT::AppLvl(Box::new(tm), awt.clone()),
                                TypeT::AppLvl(Box::new(ty), awt),
                            ))
                        }
                    }
                }
                Args::Label(Spanned(l, sp)) => {
                    let (tmt, tyt) =
                        head.check(env, &l.map_ref(&|_| NoDispOption(None)).to_map())?;
                    let (lt, tyn) = l.infer(env, local, sp)?;

                    let awt = ArgsWithTypeT {
                        args: lt,
                        ty: Box::new(tyn.quote()),
                    };

                    if let Some(t) = &args.ty {
                        t.check(env, local, &tyn)?;
                    }

                    Ok((
                        TermT::AppPath(Box::new(tmt), awt.clone()),
                        TypeT::AppPath(Box::new(tyt), awt),
                    ))
                }
            },
            t => local.ctx.check_in_tree(t, |tr| {
                let res = t.infer(env)?;
                match res {
                    Either::Left(res) => {
                        if &res.ctx != tr {
                            Err(TypeCheckError::TreeMismatch(t.clone(), res.ctx, tr.clone()))
                        } else {
                            Ok((res.tm, res.ty))
                        }
                    }
                    Either::Right(_) => Err(TypeCheckError::TermNotTree(t.clone(), tr.clone())),
                }
            }),
        }
    }
}

impl<S: Clone + Debug> Type<S> {
    pub(crate) fn infer<T: Eval>(
        &self,
        env: &Environment,
        local: &Local<T>,
    ) -> Result<(TypeT<T>, TypeN<T>), TypeCheckError<S>> {
        match self {
            Type::Base(_) => Ok((TypeT::Base, TypeN(vec![]))),
            Type::Arr(s, a, t, sp) => {
                let (st, ty1) = s.check(env, local)?;
                let (tt, ty2) = t.check(env, local)?;
                let sem_ctx = local.ctx.id_sem_ctx();
                let sn = st.eval(&sem_ctx, env);
                let ty1n = ty1.eval(&sem_ctx, env);
                let tn = tt.eval(&sem_ctx, env);
                let ty2n = ty2.eval(&sem_ctx, env);
                let (tyt, mut tyn) = if let Some(ty) = a {
                    let (tyt, tyn) = ty.infer(env, local)?;
                    if tyn != ty1n {
                        let y = ty1n.quote().to_expr(Some(&local.ctx), env.implicits);
                        return Err(TypeCheckError::InferredTypeWrong(s.clone(), y, *ty.clone()));
                    }
                    if tyn != ty2n {
                        let y = ty2n.quote().to_expr(Some(&local.ctx), env.implicits);
                        return Err(TypeCheckError::InferredTypeWrong(t.clone(), y, *ty.clone()));
                    }
                    (tyt, tyn)
                } else {
                    if ty1n != ty2n {
                        let x = ty1n.quote().to_expr(Some(&local.ctx), env.implicits);
                        let y = ty2n.quote().to_expr(Some(&local.ctx), env.implicits);
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

    pub(crate) fn check<T: Eval>(
        &self,
        env: &Environment,
        local: &Local<T>,
        ty: &TypeNRef<T>,
    ) -> Result<(), TypeCheckError<S>> {
        match self {
            Type::Hole(_) => Ok(()),
            Type::Arr(s, a, t, _) => {
                let (sn, tn) = ty.0.last().ok_or(TypeCheckError::TypeMismatch(
                    self.clone(),
                    ty.quote().to_expr(Some(&local.ctx), env.implicits),
                ))?;

                let sem_ctx = local.ctx.id_sem_ctx();
                if !matches!(s, Term::Hole(_)) {
                    let (st, _) = s.check(env, local)?;
                    let stn = st.eval(&sem_ctx, env);
                    if &stn != sn {
                        let x = sn.quote().to_expr(Some(&local.ctx), env.implicits);
                        return Err(TypeCheckError::TermMismatch(s.clone(), x));
                    }
                }

                if !matches!(t, Term::Hole(_)) {
                    let (tt, _) = t.check(env, local)?;
                    if &tt.eval(&sem_ctx, env) != tn {
                        let x = tn.quote().to_expr(Some(&local.ctx), env.implicits);
                        return Err(TypeCheckError::TermMismatch(t.clone(), x));
                    }
                }

                if let Some(inner) = a {
                    if ty.0.is_empty() {
                        return Err(TypeCheckError::TypeMismatch(self.clone(), Type::Base(())));
                    }
                    inner.check(env, local, ty.inner())?;
                }

                Ok(())
            }
            _ => {
                let (_, tyn) = self.infer(env, local)?;
                if &*tyn != ty {
                    let x = ty.quote().to_expr(Some(&local.ctx), env.implicits);
                    return Err(TypeCheckError::TypeMismatch(self.clone(), x));
                }
                Ok(())
            }
        }
    }
}

impl<S: Clone + Debug> Label<S> {
    fn from_sub<T>(sub: &Sub<S>, tree: &Tree<T>, sp: &S) -> Result<Self, TypeCheckError<S>> {
        let mut iter = sub.iter().cloned();
        tree.label_from_max(&mut iter).ok_or_else(|| {
            TypeCheckError::SubToLabel(Args::Sub(Spanned(sub.clone(), sp.clone())), sp.clone())
        })
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn infer<T: Eval>(
        &self,
        env: &Environment,
        local: &Local<T>,
        sp: &S,
    ) -> Result<(ArgsT<Path, T>, TypeN<T>), TypeCheckError<S>> {
        if self.branches.is_empty() {
            let tm = self.elements.first().unwrap();
            let term =
                tm.0.as_ref()
                    .ok_or_else(|| TypeCheckError::LocallyMaxMissing(self.clone(), sp.clone()))?;

            let (tm, ty) = term.check(env, local)?;

            return Ok((Tree::singleton(tm), ty.eval(&local.ctx.id_sem_ctx(), env)));
        }
        let mut branches = vec![];
        let mut el_norm = vec![];
        let mut ty = None;
        for br in &self.branches {
            let (l, mut ty1) = br.infer(env, local, sp)?;
            branches.push(l);

            let (s, t) = ty1
                .0
                .pop()
                .ok_or_else(|| TypeCheckError::DimensionMismatch(self.clone(), sp.clone()))?;
            if let Some(s1) = el_norm.last() {
                if &s != s1 {
                    let x = s.quote().to_expr(Some(&local.ctx), env.implicits);
                    let y = s1.quote().to_expr(Some(&local.ctx), env.implicits);
                    return Err(TypeCheckError::LabelMismatch(
                        self.clone(),
                        x,
                        y,
                        sp.clone(),
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
            .map(|(el, eln)| match &el.0 {
                Some(tm) => {
                    let tmt = tm.check(env, local)?.0;
                    let tmn = tmt.eval(&local.ctx.id_sem_ctx(), env);
                    if tmn != eln {
                        let x = eln.quote().to_expr(Some(&local.ctx), env.implicits);
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

impl<S: Clone + Debug> Ctx<S> {
    pub(crate) fn check(
        &self,
        env: &Environment,
    ) -> Result<Either<Local<Path>, Local<Level>>, TypeCheckError<S>> {
        match self {
            Ctx::Tree(tr) => Ok(Either::Left(tr.to_map())),
            Ctx::Other(ctx) => {
                let mut local: Local<Level> = Local {
                    ctx: vec![],
                    map: HashMap::new(),
                };
                for (level, (name, ty)) in ctx.iter().enumerate() {
                    let (tyt, _) = ty.infer(env, &local)?;
                    local.ctx.push((Some(name.clone()), tyt.clone()));
                    local.map.insert(name.clone(), (level, tyt));
                }

                Ok(Either::Right(local))
            }
        }
    }
}
