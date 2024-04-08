use crate::{
    common::{Path, Position},
    syntax::{
        core::{ArgsWithTypeC, TermC, TypeC},
        normal::{HeadN, TermN, TypeNRef},
    },
};

impl HeadN {
    pub(crate) fn quote(&self) -> TermC<Path> {
        match self {
            HeadN::CohN { tree, ty } => TermC::Coh(tree.clone(), Box::new(ty.quote())),
            HeadN::CompN { tree } => TermC::Comp(tree.clone()),
            HeadN::IdN { dim } => TermC::Id(*dim),
        }
    }
}

impl<T: Position> TermN<T> {
    pub(crate) fn quote(&self) -> TermC<T> {
        match self {
            TermN::Variable(x) => TermC::Var(x.clone()),
            TermN::Other(head, args) => TermC::AppPath(
                Box::new(head.quote()),
                ArgsWithTypeC {
                    args: args.map_ref(&|tm| tm.quote()),
                    ty: Box::new(TypeC::Base),
                },
            ),
        }
    }
}

impl<T: Position> TypeNRef<T> {
    pub(crate) fn quote(&self) -> TypeC<T> {
        let mut ret = TypeC::Base;

        for (s, t) in &self.0 {
            ret = TypeC::Arr(s.quote(), Box::new(ret), t.quote())
        }

        ret
    }
}
