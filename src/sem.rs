use slab::Slab;
use std::collections::HashMap;

use crate::syn::{Ident, NodeId, Ast, NodeMap};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct PackageId(pub usize);

impl PackageId {
    pub fn null() -> Self {
        Self(usize::max_value())
    }
}

pub struct Package {
    pub name: Ident,
    pub ast: Ast,
}

pub struct Scope {
    pub symbols: HashMap<Ident, NodeId>,
}

pub struct Context<'a> {
    pub packages: Slab<Package>,
    pub package_by_name: HashMap<Ident, PackageId>,
    pub ast: &'a Ast,
}

pub struct Semantic {
    scopes: NodeMap<Scope>,
}

impl Semantic {
    pub fn new() -> Self {
        Self {
            scopes: Default::default(),
        }
    }

    pub fn run(&mut self, ctx: &Context) {
        self.visit_node(ctx.ast.root.value, ctx);
    }

    fn visit_node(&mut self, node: NodeId, ctx: &Context) {
        // match ctx.ast.node_kind(node) {
        //
        // }
    }
}