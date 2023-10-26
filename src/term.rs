use crate::{
    common::{Name, Pos, Tree},
    normal::{TermN, TypeN},
    typecheck::SemCtx,
};

pub enum TermT {
    App(Box<TermT>, ArgsT, Box<TypeT>),
    Var(Pos),
    TopLvl(Name, TermN),
    Susp(Box<TermT>),
    Coh(Tree<()>, Box<TypeT>),
}

pub enum ArgsT {
    Sub(Vec<TermT>),
    Label(Tree<TermT>),
}

pub enum TypeT {
    Base,
    Arr(TermT, Box<TypeT>, TermT),
}

pub enum CtxT {
    Tree(Tree<()>),
    Other(Vec<TypeT>),
}

impl TermT {
    pub fn eval(&self, ctx: &SemCtx) -> TermN {
        match &self {
            TermT::App(t, args, ty) => t.eval(&args.eval(ty, ctx)),
            TermT::Var(pos) => ctx.get(pos),
            TermT::TopLvl(_, _) => todo!(),
            TermT::Susp(t) => todo!(),
            TermT::Coh(_, _) => todo!(),
            TermT::Meta(idx) => TermN::Meta(*idx),
        }
    }
}

impl TypeT {
    pub fn eval(&self, ctx: &SemCtx) -> TypeN {
        match &self {
            TypeT::Meta(idx) => TypeN::Meta(*idx),
            TypeT::Base => ctx.get_ty().clone(),
            TypeT::Arr(s, a, t) => {
		TypeN::Arr(s.eval(ctx), Box::new(a.eval(ctx)), t.eval(ctx))
	    },
        }
    }
}

impl ArgsT {
    pub fn eval(&self, ty: &TypeT, ctx: &SemCtx) -> SemCtx {
        match self {
            ArgsT::Sub(ts) => {
                let map = ts
                    .iter()
                    .enumerate()
                    .map(|(i, t)| (Pos::Level(i), t.eval(ctx)))
                    .collect();
                let tyn = ty.eval(ctx);
                SemCtx::new(map, tyn)
            }
            ArgsT::Label(tr) => {
		let pairs = tr.get_paths();

		let map = pairs.into_iter().map(|(path,tm)| {
		    (Pos::Path(path), tm.eval(ctx))
		}).collect();

		let tyn = ty.eval(ctx);
		SemCtx::new(map, tyn)
	    },
        }
    }
}
