use std::{collections::HashMap, fmt::Debug, hash::Hash, ops::Range};

use ariadne::{Color, Fmt, Report, ReportKind, Span};
use either::Either;
use thiserror::Error;

use crate::{
    common::{
        Ctx, Eval, InferRes, InferResEither, Level, Name, NoDispOption, Path, Position, Signature,
        Spanned, Tree,
    },
    syntax::{
        core::{ArgsC, ArgsWithTypeC, TermC, TypeC},
        normal::{TypeN, TypeNRef},
        raw::{ArgsR, ArgsWithTypeR, CtxR, LabelR, SubR, TermR, TermRS, TypeR, TypeRS},
    },
};

pub(crate) struct Local<T: Position> {
    pub(crate) ctx: T::Ctx,
    pub(crate) map: HashMap<Name, (T, TypeC<T>)>,
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
    #[error("Unknown top level name: \"{}\"", .0.fg(Color::Red))]
    UnknownTopLevel(Name, S),
    #[error("Unknown local variable: \"{}\"", .0.fg(Color::Red))]
    UnknownLocal(Name, S),
    #[error("Type \"{}\" does not satisfy fullness condition", .0.fg(Color::Red))]
    Fullness(TypeRS<S>),
    #[error("Cannot infer context for term \"{}\"", .0.fg(Color::Red))]
    CannotInferCtx(TermRS<S>),
    #[error("Term \"{}\" lives over a tree", .0.fg(Color::Red))]
    TermExistsInTree(TermRS<S>),
    #[error("Identity does not exist in context \"{}\"", .1.fg(Color::Red))]
    IdNotDisc(S, Tree<NoDispOption<Name>>),
    #[error("Type \"{}\" is not checkable", .0.fg(Color::Red))]
    CannotCheck(TypeRS<S>),
    #[error("Terms \"{}\" and \"{}\" do not have matching types", .0.fg(Color::Blue), .2.fg(Color::Magenta))]
    InferredTypesNotEqual(TermRS<S>, TypeRS<()>, TermRS<S>, TypeRS<()>, S),
    #[error("Term \"{}\" had inferred type \"{}\" but should have type \"{}\"", .0.fg(Color::Red), .1.fg(Color::Red), .2.fg(Color::Green))]
    InferredTypeWrong(TermRS<S>, TypeRS<()>, TypeRS<S>),
    #[error("Term \"{}\" had inferred type \"{}\" but should have type \"{}\"", .0.fg(Color::Red), .1.fg(Color::Red), .2.fg(Color::Green))]
    InferredTypeWrongCalc(TermRS<S>, TypeRS<()>, TypeRS<()>),
    #[error("Given type \"{}\" does not match inferred type \"{}\"", .0.fg(Color::Red), .1.fg(Color::Green))]
    TypeMismatch(TypeRS<S>, TypeRS<()>),
    #[error("Given term \"{}\" does not match inferred term \"{}\"", .0.fg(Color::Red), .1.fg(Color::Green))]
    TermMismatch(TermRS<S>, TermRS<()>),
    #[error("Mismatch between inferred terms \"{}\" and \"{}\" in labelling \"{}\"", .1.fg(Color::Magenta), .2.fg(Color::Blue), .0.fg(Color::Red))]
    LabelMismatch(LabelR<S>, TermRS<()>, TermRS<()>, S),
    #[error("Dimension mismatch in labeling \"{}\"", .0.fg(Color::Red))]
    DimensionMismatch(LabelR<S>, S),
    #[error("Substitution \"{}\" cannot be coerced to labelling", .0.fg(Color::Red))]
    SubToLabel(ArgsWithTypeR<S>),
    #[error("Term \"{}\" should live over tree \"{}\"", .0.fg(Color::Red), .1.fg(Color::Green))]
    TermNotTree(TermRS<S>, Tree<NoDispOption<Name>>),
    #[error("Locally maximal argument missing from labelling \"{}\"", .0.fg(Color::Red))]
    LocallyMaxMissing(LabelR<S>, S),
    #[error("Term \"{}\" lives in context \"{}\" but inferred context was \"{}\"", .0.fg(Color::Red), .1.fg(Color::Red), .2.fg(Color::Green))]
    TreeMismatch(
        TermRS<S>,
        Tree<NoDispOption<Name>>,
        Tree<NoDispOption<Name>>,
    ),
    #[error("Term \"{}\" was given the wrong number of arguments", .0.fg(Color::Red))]
    WrongArgs(TermRS<S>, usize, S, usize),
    #[error("Cannot check hole")]
    Hole(S),
}

impl TypeCheckError<Range<usize>> {
    fn span(&self) -> &Range<usize> {
        match self {
            TypeCheckError::UnknownTopLevel(_, s)
            | TypeCheckError::UnknownLocal(_, s)
            | TypeCheckError::InferredTypesNotEqual(_, _, _, _, s)
            | TypeCheckError::LabelMismatch(_, _, _, s)
            | TypeCheckError::DimensionMismatch(_, s)
            | TypeCheckError::LocallyMaxMissing(_, s)
            | TypeCheckError::Hole(s)
            | TypeCheckError::WrongArgs(_, _, s, _)
            | TypeCheckError::IdNotDisc(s, _) => s,
            TypeCheckError::SubToLabel(args) => &args.sp,
            TypeCheckError::Fullness(ty)
            | TypeCheckError::TypeMismatch(ty, _)
            | TypeCheckError::CannotCheck(ty) => &ty.1,
            TypeCheckError::CannotInferCtx(tm)
            | TypeCheckError::TermExistsInTree(tm)
            | TypeCheckError::InferredTypeWrong(tm, _, _)
            | TypeCheckError::InferredTypeWrongCalc(tm, _, _)
            | TypeCheckError::TermMismatch(tm, _)
            | TypeCheckError::TreeMismatch(tm, _, _)
            | TypeCheckError::TermNotTree(tm, _) => &tm.1,
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
                ariadne::Label::new((src.clone(), ty.1.clone()))
                    .with_message("Type is not full")
                    .with_color(Color::Red),
            ),
            TypeCheckError::CannotInferCtx(tm) => report.add_label(
                ariadne::Label::new((src.clone(), tm.1.clone()))
                    .with_message("Context cannot be inferred")
                    .with_color(Color::Red),
            ),
            TypeCheckError::TermExistsInTree(tm) => report.add_label(
                ariadne::Label::new((src.clone(), tm.1.clone()))
                    .with_message("Term can only occur in disc contexts")
                    .with_color(Color::Red),
            ),
            TypeCheckError::IdNotDisc(sp, _) => report.add_label(
                ariadne::Label::new((src.clone(), sp))
                    .with_message("id can only occur in disc contexts")
                    .with_color(Color::Red),
            ),
            TypeCheckError::CannotCheck(ty) => report.add_label(
                ariadne::Label::new((src.clone(), ty.1.clone()))
                    .with_message("Type is not checkable")
                    .with_color(Color::Red),
            ),
            TypeCheckError::InferredTypesNotEqual(tm1, ty1, tm2, ty2, _) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), tm2.1.clone()))
                        .with_message(format!("Has type {}", ty2.fg(Color::Magenta)))
                        .with_order(0)
                        .with_color(Color::Magenta),
                );
                report.add_label(
                    ariadne::Label::new((src.clone(), tm1.1.clone()))
                        .with_message(format!("Has type {}", ty1.fg(Color::Blue)))
                        .with_order(1)
                        .with_color(Color::Blue),
                );
            }
            TypeCheckError::InferredTypeWrong(tm, ity, gty) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), tm.1.clone()))
                        .with_message(format!("Term has inferred type {}", ity.fg(Color::Red)))
                        .with_color(Color::Red),
                );
                report.add_label(
                    ariadne::Label::new((src.clone(), gty.1.clone()))
                        .with_message(format!("Term should have type {}", gty.fg(Color::Green)))
                        .with_color(Color::Green),
                );
            }
            TypeCheckError::InferredTypeWrongCalc(tm, ity, gty) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), tm.1.clone()))
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
                    ariadne::Label::new((src.clone(), ty.1.clone()))
                        .with_message("Given type")
                        .with_color(Color::Red),
                );
            }
            TypeCheckError::TermMismatch(tm, _) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), tm.1.clone()))
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
            TypeCheckError::SubToLabel(args) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), args.sp))
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
                ariadne::Label::new((src.clone(), t.1.clone()))
                    .with_message("Term does not live over tree context")
                    .with_color(Color::Red),
            ),
            TypeCheckError::TreeMismatch(t, _, _) => report.add_label(
                ariadne::Label::new((src.clone(), t.1.clone()))
                    .with_message("Term does not live over correct tree")
                    .with_color(Color::Red),
            ),
            TypeCheckError::WrongArgs(t, x, sp, y) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), t.1.clone()))
                        .with_message(format!("Term expected {x} arguments"))
                        .with_color(Color::Red),
                );
                report.add_label(
                    ariadne::Label::new((src.clone(), sp))
                        .with_message(format!("and was given {y} arguments"))
                        .with_color(Color::Green),
                );
            }
            TypeCheckError::Hole(sp) => report.add_label(
                ariadne::Label::new((src.clone(), sp))
                    .with_message("Hole cannot be inferred")
                    .with_color(Color::Red),
            ),
        }
        report.finish()
    }
}

impl<S: Clone + Debug> TermRS<S> {
    pub(crate) fn infer(&self, env: &Signature) -> Result<InferResEither, TypeCheckError<S>> {
        match &self.0 {
            TermR::Hole => Err(TypeCheckError::Hole(self.1.clone())),
            TermR::Susp(t) => {
                let res = t.infer(env)?;
                Ok(res.map_either(InferRes::susp, InferRes::susp))
            }
            TermR::Var(x) => env
                .top_level
                .get(x)
                .cloned()
                .map(|res| {
                    res.map_either(
                        |r| InferRes {
                            ctx: r.ctx,
                            tm: TermC::TopLvl(x.clone(), Box::new(r.tm)),
                            ty: r.ty,
                        },
                        |r| InferRes {
                            ctx: r.ctx,
                            tm: TermC::TopLvl(x.clone(), Box::new(r.tm)),
                            ty: r.ty,
                        },
                    )
                })
                .ok_or(TypeCheckError::UnknownTopLevel(x.clone(), self.1.clone())),
            TermR::Coh(tr, ty) => {
                let (tyt, tyn) = ty.infer(env, &tr.to_map())?;

                if !tyn.support_check(tr, &env.support) {
                    return Err(TypeCheckError::Fullness(*ty.clone()));
                }

                Ok(Either::Left(InferRes {
                    ctx: tr.clone(),
                    tm: TermC::Coh(tr.clone(), Box::new(tyt.clone())),
                    ty: tyt,
                }))
            }
            TermR::Id => Ok(Either::Left(InferRes {
                ctx: Tree::singleton(NoDispOption(None)),
                tm: TermC::Id(0),
                ty: TypeC::Arr(
                    TermC::Var(Path::here(0)),
                    Box::new(TypeC::Base),
                    TermC::Var(Path::here(0)),
                ),
            })),
            _ => Err(TypeCheckError::CannotInferCtx(self.clone())),
        }
    }

    pub(crate) fn check<T: Eval>(
        &self,
        env: &Signature,
        local: &Local<T>,
    ) -> Result<(TermC<T>, TypeC<T>), TypeCheckError<S>> {
        match &self.0 {
            TermR::Hole => Err(TypeCheckError::Hole(self.1.clone())),
            TermR::Var(x) if !local.map.contains_key(x) && !env.top_level.contains_key(x) => {
                Err(TypeCheckError::UnknownLocal(x.clone(), self.1.clone()))
            }
            TermR::Var(x) if local.map.contains_key(x) => local
                .map
                .get(x)
                .map(|(p, ty)| (TermC::Var(p.clone()), ty.clone()))
                .ok_or_else(|| TypeCheckError::UnknownLocal(x.clone(), self.1.clone())),
            TermR::Comp => local.ctx.check_in_tree(self, |tr| {
                Ok((TermC::Comp(tr.clone()), tr.standard_type(tr.dim())))
            }),
            TermR::Id => local.ctx.check_in_tree(self, |tr| {
                if tr.is_disc() {
                    let d = tr.dim();
                    Ok((TermC::Id(d), tr.standard_type(d + 1)))
                } else {
                    Err(TypeCheckError::IdNotDisc(self.1.clone(), tr.clone()))
                }
            }),
            TermR::App(head, args) => match &args.args {
                ArgsR::Sub(sub) => {
                    let res = head.infer(env)?;
                    match res {
                        Either::Left(InferRes { ctx, tm, ty }) => {
                            let label = LabelR::from_sub(sub, &args.ty, &ctx, &args.sp)?;
                            let (l, lty) = label.infer(env, local, &args.sp)?;

                            if let Some(t) = &args.ty {
                                t.check(env, local, &lty)?;
                            }

                            let awt = ArgsWithTypeC {
                                args: l,
                                ty: Box::new(lty.quote()),
                            };

                            Ok((
                                TermC::AppLabel(Box::new(tm), awt.clone()),
                                TypeC::AppPath(Box::new(ty), awt),
                            ))
                        }
                        Either::Right(InferRes { ctx, tm, ty }) => {
                            if sub.len() != ctx.len() {
                                return Err(TypeCheckError::WrongArgs(
                                    *head.clone(),
                                    ctx.len(),
                                    args.sp.clone(),
                                    sub.len(),
                                ));
                            }
                            let (subt, tys): (Vec<TermC<T>>, Vec<_>) = sub
                                .iter()
                                .map(|t| Ok((t.check(env, local)?, t)))
                                .collect::<Result<Vec<_>, _>>()?
                                .into_iter()
                                .map(|((tt, ty), tm)| (tt, (ty, tm)))
                                .unzip();
                            let awt = ArgsWithTypeC {
                                args: subt,
                                ty: Box::new(tys[0].0.clone()),
                            };

                            let sem_ctx = local.ctx.id_sem_ctx();

                            let args_sem_ctx = awt.eval(&sem_ctx, env);

                            for (x, (y, tm)) in ctx.iter().map(|x| &x.1).zip(tys) {
                                let xn = x.eval(&args_sem_ctx, env);
                                let yn = y.eval(&sem_ctx, env);
                                if xn != yn {
                                    let xe = xn.quote().to_raw(Some(&local.ctx), env.implicits);
                                    let ye = yn.quote().to_raw(Some(&local.ctx), env.implicits);
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
                                TermC::AppSub(Box::new(tm), awt.clone()),
                                TypeC::AppLvl(Box::new(ty), awt),
                            ))
                        }
                    }
                }
                ArgsR::Label(l) => {
                    let (tmt, tyt) = head.check(
                        env,
                        &l.path_tree()
                            .map(&|p| NoDispOption(Some(p.to_name())))
                            .to_map(),
                    )?;
                    let (lt, tyn) = l.infer(env, local, &args.sp)?;

                    let awt = ArgsWithTypeC {
                        args: lt,
                        ty: Box::new(tyn.quote()),
                    };

                    if let Some(t) = &args.ty {
                        t.check(env, local, &tyn)?;
                    }

                    Ok((
                        TermC::AppLabel(Box::new(tmt), awt.clone()),
                        TypeC::AppPath(Box::new(tyt), awt),
                    ))
                }
            },
            _ => local.ctx.check_in_tree(self, |tr| {
                let res = self.infer(env)?;
                match res {
                    Either::Left(res) => {
                        if &res.ctx != tr {
                            Err(TypeCheckError::TreeMismatch(
                                self.clone(),
                                res.ctx,
                                tr.clone(),
                            ))
                        } else {
                            Ok((res.tm, res.ty))
                        }
                    }
                    Either::Right(_) => Err(TypeCheckError::TermNotTree(self.clone(), tr.clone())),
                }
            }),
        }
    }
}

impl<S: Clone + Debug> TypeRS<S> {
    pub(crate) fn infer<T: Eval>(
        &self,
        env: &Signature,
        local: &Local<T>,
    ) -> Result<(TypeC<T>, TypeN<T>), TypeCheckError<S>> {
        match &self.0 {
            TypeR::Base => Ok((TypeC::Base, TypeN(vec![]))),
            TypeR::Arr(s, a, t) => {
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
                        let y = ty1n.quote().to_raw(Some(&local.ctx), env.implicits);
                        return Err(TypeCheckError::InferredTypeWrong(s.clone(), y, *ty.clone()));
                    }
                    if tyn != ty2n {
                        let y = ty2n.quote().to_raw(Some(&local.ctx), env.implicits);
                        return Err(TypeCheckError::InferredTypeWrong(t.clone(), y, *ty.clone()));
                    }
                    (tyt, tyn)
                } else {
                    if ty1n != ty2n {
                        let x = ty1n.quote().to_raw(Some(&local.ctx), env.implicits);
                        let y = ty2n.quote().to_raw(Some(&local.ctx), env.implicits);
                        return Err(TypeCheckError::InferredTypesNotEqual(
                            s.clone(),
                            x,
                            t.clone(),
                            y,
                            self.1.clone(),
                        ));
                    }
                    (ty1n.quote(), ty1n)
                };

                tyn.0.push((sn, tn));
                Ok((TypeC::Arr(st, Box::new(tyt), tt), tyn))
            }
            _ => Err(TypeCheckError::CannotCheck(self.clone())),
        }
    }

    pub(crate) fn check<T: Eval>(
        &self,
        env: &Signature,
        local: &Local<T>,
        ty: &TypeNRef<T>,
    ) -> Result<(), TypeCheckError<S>> {
        match &self.0 {
            TypeR::Hole => Ok(()),
            TypeR::Arr(s, a, t) => {
                let (sn, tn) = ty.0.last().ok_or(TypeCheckError::TypeMismatch(
                    self.clone(),
                    ty.quote().to_raw(Some(&local.ctx), env.implicits),
                ))?;

                let sem_ctx = local.ctx.id_sem_ctx();
                if !matches!(s.0, TermR::Hole) {
                    let (st, _) = s.check(env, local)?;
                    let stn = st.eval(&sem_ctx, env);
                    if &stn != sn {
                        let x = sn.quote().to_raw(Some(&local.ctx), env.implicits);
                        return Err(TypeCheckError::TermMismatch(s.clone(), x));
                    }
                }

                if !matches!(t.0, TermR::Hole) {
                    let (tt, _) = t.check(env, local)?;
                    if &tt.eval(&sem_ctx, env) != tn {
                        let x = tn.quote().to_raw(Some(&local.ctx), env.implicits);
                        return Err(TypeCheckError::TermMismatch(t.clone(), x));
                    }
                }

                if let Some(inner) = a {
                    if ty.0.is_empty() {
                        return Err(TypeCheckError::TypeMismatch(
                            self.clone(),
                            Spanned(TypeR::Base, ()),
                        ));
                    }
                    inner.check(env, local, ty.inner())?;
                }

                Ok(())
            }
            _ => {
                let (_, tyn) = self.infer(env, local)?;
                if &*tyn != ty {
                    let x = ty.quote().to_raw(Some(&local.ctx), env.implicits);
                    return Err(TypeCheckError::TypeMismatch(self.clone(), x));
                }
                Ok(())
            }
        }
    }
}

impl<S: Clone + Debug> LabelR<S> {
    fn from_sub<T>(
        sub: &SubR<S>,
        ty: &Option<Box<TypeRS<S>>>,
        tree: &Tree<T>,
        sp: &S,
    ) -> Result<Self, TypeCheckError<S>> {
        let mut iter = sub.iter().cloned();
        tree.label_from_max(&mut iter).ok_or_else(|| {
            TypeCheckError::SubToLabel(ArgsWithTypeR {
                args: ArgsR::Sub(sub.clone()),
                ty: ty.clone(),
                sp: sp.clone(),
            })
        })
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn infer<T: Eval>(
        &self,
        env: &Signature,
        local: &Local<T>,
        sp: &S,
    ) -> Result<(ArgsC<Path, T>, TypeN<T>), TypeCheckError<S>> {
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
                    let x = s.quote().to_raw(Some(&local.ctx), env.implicits);
                    let y = s1.quote().to_raw(Some(&local.ctx), env.implicits);
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
                        let x = eln.quote().to_raw(Some(&local.ctx), env.implicits);
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

impl<S: Clone + Debug> CtxR<S> {
    pub(crate) fn check(
        &self,
        env: &Signature,
    ) -> Result<Either<Local<Path>, Local<Level>>, TypeCheckError<S>> {
        match self {
            CtxR::Tree(tr) => Ok(Either::Left(tr.to_map())),
            CtxR::Other(ctx) => {
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
