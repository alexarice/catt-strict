use std::fmt::Debug;
use std::hash::Hash;
use std::{collections::HashMap, ops::Range};

use ariadne::{Color, Fmt, Report, ReportKind, Span};
use itertools::Itertools;
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
    #[error("Cannot convert labelling \"{}\" to substitution", .0.fg(Color::Red))]
    LabelToSub(Label<S>, S),
    #[error("Locally maximal argument missing from labelling \"{}\"", .0.fg(Color::Red))]
    LocallyMaxMissing(Label<S>, S),
    #[error("Dimension sequence \"{}\" does not correspond to pasting diagram",
	    .0.iter().map(ToString::to_string).join(" ").fg(Color::Red))]
    BadDimSeq(Vec<usize>, S),
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
            | TypeCheckError::LocallyMaxMissing(_, s)
            | TypeCheckError::BadDimSeq(_, s) => s,
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
    pub fn to_report<Id>(self, src: &Id) -> Report<'static, (Id, Range<usize>)>
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
            TypeCheckError::LabelToSub(_, sp) => {
                report.add_label(
                    ariadne::Label::new((src.clone(), sp))
                        .with_message("Label found when substitution expected")
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
            TypeCheckError::BadDimSeq(_, sp) => report.add_label(
                ariadne::Label::new((src.clone(), sp))
                    .with_message("Dimension sequence malformed")
                    .with_color(Color::Red),
            ),
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
            Term::UComp(tr, _) => {
                let ty = tr.unbiased_type(tr.dim());
                Ok((
                    CtxT::Tree(tr.clone()),
                    TermT::UComp(tr.clone(), Box::new(ty.clone())),
                    ty,
                ))
            }
            Term::UCompNum(v, inner, _) => {
                let tr = Tree::from_usizes(v)
                    .ok_or_else(|| TypeCheckError::BadDimSeq(v.clone(), inner.clone()))?;
                let ty = tr.unbiased_type(tr.dim());
                Ok((
                    CtxT::Tree(tr.clone()),
                    TermT::UComp(tr, Box::new(ty.clone())),
                    ty,
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
        tree.label_from_max(&mut iter).ok_or_else(|| {
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
            let tm = self.elements.first().unwrap();
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
        for br in &self.branches {
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
