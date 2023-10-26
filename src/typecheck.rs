// use std::collections::HashMap;

// use thiserror::Error;
// use union_find::{QuickFindUf, UnionByRank, UnionFind};

// use crate::{
//     common::{Name, NoDispOption, Pos, Tree},
//     normal::{CtxN, TermN, TypeN},
//     syntax::{Term, Type},
//     term::TermT,
// };

// pub enum Constraint {
//     TypeEq(TypeN, TypeN),
//     TermEq(TermN, TermN),
//     Full(Tree<()>, TypeN),
// }

// pub struct Environment {
//     top_level: HashMap<Name, (TermN, CtxN, TypeN)>,
//     meta_tm: QuickFindUf<UnionByRank>,
//     meta_tm_map: HashMap<usize, TermN>,
//     meta_ty: QuickFindUf<UnionByRank>,
//     meta_ty_map: HashMap<usize, TypeN>,
//     constraints: Vec<Constraint>,
// }

use std::collections::HashMap;

use thiserror::Error;

use crate::{
    common::{Name, Pos},
    normal::{CtxN, TermN, TypeN},
    syntax::{Args, Head, Term, Type},
    term::{ArgsT, TermT, TypeT},
};

pub struct Environment {
    top_level: HashMap<Name, (CtxN, TermN, TypeN)>,
    local: HashMap<Name, (Pos, TypeN)>,
}

pub struct SemCtx {
    map: HashMap<Pos, TermN>,
    ty: TypeN,
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
}

impl Term {
    pub fn infer(&self, env: &Environment) -> Result<(TermT, TypeN), TypeCheckError> {
        match &self {
            Term::Var(x) => env
                .local
                .get(x)
                .map(|(p, ty)| (TermT::Var(p.clone()), ty.clone()))
                .ok_or(TypeCheckError::UnknownVariable(x.clone())),
            Term::WithArgs(head, args, ty) => {
                let (ctx, tm, ty) = head.infer(env)?;

                Ok((TermT::App(Box::new(tm), todo!(), todo!()), todo!()))
            }
        }
    }
}

impl Head {
    pub fn infer(&self, env: &Environment) -> Result<(CtxN, TermT, TypeN), TypeCheckError> {
        match &self {
            Head::Susp(t) => {
                let (ctx, tm, ty) = t.infer(env)?;
                Ok((todo!(), TermT::Susp(Box::new(tm)), todo!()))
            }
            Head::TopLvl(x) => env
                .top_level
                .get(x)
                .cloned()
                .map(|(ctx, tm, ty)| (ctx, TermT::TopLvl(x.clone(), tm), ty))
                .ok_or(TypeCheckError::UnknownTopLevel(x.clone())),
            Head::Coh(tr, ty) => {
                todo!()
            }
        }
    }
}

impl Type {
    pub fn check(&self, env: &Environment) -> Result<TypeT, TypeCheckError> {
        match self {
            Type::Base => Ok(TypeT::Base),
            Type::Arr(s, a, t) => {
                let (st, ty1) = s.infer(env)?;
                let (tt, ty2) = t.infer(env)?;
                match a.map(|x| x) {
                    Some(ty) => {
                        let (tyt, tyn) = ty.check_norm(env)?;
                        if ty1 != tyn {
                            Err(TypeCheckError::TypeMismatch(ty1, tyn))
                        } else if ty2 != tyn {
                            Err(TypeCheckError::TypeMismatch(ty2, tyn))
                        } else {
                            Ok(TypeT::Arr(st, Box::new(tyt), tt))
                        }
                    }
                    None => {
                        if ty1 != ty2 {
                            Err(TypeCheckError::TypeMismatch(ty1, ty2))
                        } else {
                            Ok(TypeT::Arr(st, todo!(), tt))
                        }
                    }
                }
            }
        }
    }

    pub fn check_norm(&self, env: &Environment) -> Result<(TypeT, TypeN), TypeCheckError> {
        match self {
            Type::Base => Ok((TypeT::Base, TypeN::Base)),
            Type::Arr(s, a, t) => {
                let (st, ty1) = s.infer(env)?;
                let (tt, ty2) = t.infer(env)?;
                match a.map(|x| x) {
                    Some(ty) => {
                        let (tyt, tyn) = ty.check_norm(env)?;
                        if ty1 != tyn {
                            Err(TypeCheckError::TypeMismatch(ty1, tyn))
                        } else if ty2 != tyn {
                            Err(TypeCheckError::TypeMismatch(ty2, tyn))
                        } else {
                            Ok((
                                TypeT::Arr(st, Box::new(tyt), tt),
                                TypeN::Arr(todo!(), Box::new(tyn), todo!()),
                            ))
                        }
                    }
                    None => {
			if ty1 != ty2 {
                            Err(TypeCheckError::TypeMismatch(ty1, ty2))
                        } else {
                            Ok((TypeT::Arr(st, todo!(), tt), TypeN::Arr(todo!(), Box::new(ty1), todo!())))
                        }
		    },
                }
            }
        }
    }
}

impl Args {
    pub fn infer(&self, env: &Environment, ctx: &CtxN) -> Result<(ArgsT, TypeN), TypeCheckError> {
        match (ctx, self) {
            (CtxN::Ctx(_), Args::Sub(_)) => todo!(),
            (CtxN::Ctx(_), Args::Label(_)) => Err(TypeCheckError::LabelSub),
            (CtxN::Tree(_), Args::Sub(_)) => todo!(),
            (CtxN::Tree(_), Args::Label(_)) => todo!(),
        }
    }
}

// impl SemCtx {
//     pub fn new(map: HashMap<Pos, TermN>, ty: TypeN) -> Self {
//         SemCtx { map, ty }
//     }
//     pub fn get(&self, pos: &Pos) -> TermN {
//         self.map.get(pos).unwrap().clone()
//     }
//     pub fn get_ty(&self) -> &TypeN {
//         &self.ty
//     }
// }

// #[derive(Error, Debug)]
// pub enum TypeCheckError {
//     #[error("Context cannot be inferred for {0}")]
//     InferCtxError(Term),
//     #[error("Variable {0} used twice in ctx")]
//     ReusedVariable(Name),
//     #[error("Cannot unify {0:?} and {1:?}")]
//     CannotUnify(TypeN, TypeN),
//     #[error("Will not attempt to unify terms {0:?} and {1:?}")]
//     WillNotUnify(TermN, TermN),
// }

// impl Tree<NoDispOption<Name>> {
//     pub fn check_tree(&self) -> Result<CtxN, TypeCheckError> {
//         let pairs = self.get_paths();

//         let map = pairs
//             .into_iter()
//             .filter_map(|(path, n)| n.0.as_ref().map(|name| (name.clone(), path)))
//             .collect();
//         Ok(CtxN::Tree(self.clone(), map))
//     }
// }

// impl Environment {
//     pub fn infer_ctx_term(&mut self, term: &Term) -> Result<(TermT, CtxN, TypeN), TypeCheckError> {
//         match term {
//             Term::Susp(t) => {
//                 let (tm, ctx, ty) = self.infer_ctx_term(t)?;
//                 Ok((TermT::Susp(Box::new(tm)), todo!(), todo!()))
//             }
//             Term::Coh(tr, ty) => {
//                 let ctx = tr.check_tree()?;
//                 todo!()
//             }
//             Term::Var(name) => {
//                 let (tm, ctx, ty) = self
//                     .top_level
//                     .get(name)
//                     .ok_or(TypeCheckError::InferCtxError(term.clone()))?;
//                 Ok((
//                     TermT::TopLvl(name.clone(), tm.clone()),
//                     ctx.clone(),
//                     ty.clone(),
//                 ))
//             }
//             _ => Err(TypeCheckError::InferCtxError(term.clone())),
//         }
//     }

//     pub fn check_type(&mut self, ctx: &CtxN, ty: &Type) -> Result<TypeN, TypeCheckError> {
//         match ty {
//             Type::Meta => {
//                 let idx = self.meta_ty.insert(Default::default());
//                 Ok(TypeN::Meta(idx))
//             }
//             Type::Base => Ok(TypeN::Base),
//             Type::Arr(s, a, t) => {
//                 let tyn = if let Some(ty) = a {
//                     self.check_type(ctx, ty)?
//                 } else {
//                     TypeN::Meta(self.meta_ty.insert(Default::default()))
//                 };

//                 let st = self.check_term(ctx, s, &tyn)?;
//                 let tt = self.check_term(ctx, t, &tyn)?;

//                 todo!()
//             }
//         }
//     }

//     pub fn check_term(
//         &mut self,
//         ctx: &CtxN,
//         tm: &Term,
//         ty: &TypeN,
//     ) -> Result<TermT, TypeCheckError> {
//         match self.infer_ctx_term(tm) {
//             Ok((tmt, ctx2, ty2)) => {
//                 todo!()
//             }
//             Err(TypeCheckError::InferCtxError(_)) => match tm {
//                 Term::App(s, args, ty) => {
//                     todo!()
//                 }
//                 Term::Var(name) => {
//                     todo!()
//                 }
//                 Term::Susp(_) => todo!(),
//                 Term::Coh(_, _) => unreachable!(),
//                 Term::Hole => todo!(),
//             },
//             Err(e) => Err(e),
//         }
//     }

//     pub fn resolve_ty(&mut self, a: TypeN) -> TypeN {
//         match a {
//             TypeN::Meta(i) => self
//                 .meta_ty_map
//                 .get(&i)
//                 .cloned()
//                 .unwrap_or(TypeN::Meta(self.meta_ty.find(i))),
// 	    _ => a
//         }
//     }

//     pub fn resolve_tm(&mut self, s: TermN) -> TermN {
// 	match s {
//             TermN::Meta(i) => self
//                 .meta_tm_map
//                 .get(&i)
//                 .cloned()
//                 .unwrap_or(TermN::Meta(self.meta_ty.find(i))),
// 	    _ => s
//         }
//     }

//     pub fn unify_type(&mut self, a: TypeN, b: TypeN) -> Result<(), TypeCheckError> {
//         match (self.resolve_ty(a), self.resolve_ty(b)) {
//             (TypeN::Meta(i), TypeN::Meta(j)) => {
//                 self.meta_ty.union(i, j);
//                 Ok(())
//             }
//             (TypeN::Meta(i), b2) => {
// 		self.meta_ty_map.insert(i, b2);
// 		Ok(())
// 	    }
// 	    (a2, TypeN::Meta(j)) => {
// 		self.meta_ty_map.insert(j, a2);
// 		Ok(())
// 	    }
// 	    (TypeN::Base, TypeN::Base) => Ok(()),
// 	    (TypeN::Arr(s1, base1, t1), TypeN::Arr(s2, base2, t2)) => {
// 		self.unify_type(base1, base2)?;
// 		self.unify_term(s1, s2)?;
// 		self.unify_term(t1, t2)?;
// 	    }
// 	    (a2,b2) => Err(TypeCheckError::CannotUnify(a2, b2)),
//         }
//     }

//     pub fn resolve_tm_full(&mut self, s: TermN) -> TermN {
// 	match self.resolve_tm(s) {
// 	    TermN::Variable(_) => todo!(),
// 	    TermN::Meta(_) => todo!(),
// 	    TermN::Other(head, _) => todo!(),
// 	}
//     }

//     pub fn unify_term(&mut self, a: TermN, b: TermN) -> Result<(), TypeCheckError> {
// 	match (self.resolve_tm(a), self.resolve_tm(b)) {
// 	    (TermN::Meta(i), TermN::Meta(j)) => {
//                 self.meta_tm.union(i, j);
//                 Ok(())
//             }
//             (TermN::Meta(i), b2) => {
// 		self.meta_tm_map.insert(i, b2);
// 		Ok(())
// 	    }
// 	    (a2, TermN::Meta(j)) => {
// 		self.meta_tm_map.insert(j, a2);
// 		Ok(())
// 	    }
// 	    (a2, b2) => {
// 		if a2 == b2 {
// 		    Ok(())
// 		} else {
// 		    Err(TypeCheckError::WillNotUnify(a2, b2))
// 		}
// 	    }
// 	}
//     }
// }
