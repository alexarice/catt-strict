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
            HeadN::Coh { tree, ty } => TermC::Coh(tree.clone(), Box::new(ty.quote())),
            HeadN::Comp { tree } => TermC::Comp(tree.clone()),
            HeadN::Id { dim } => TermC::Id(*dim),
        }
    }
}

impl<T: Position> TermN<T> {
    pub(crate) fn quote(&self) -> TermC<T> {
        match self {
            TermN::Variable(x) => TermC::Var(x.clone()),
            TermN::Other(head, args) => TermC::AppLabel(
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
