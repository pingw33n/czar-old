use crate::syntax::*;
use crate::syntax::traverse::*;
use super::discover_names::{MaintainNameScope, Names, NsKind};

pub struct ResolvedName {
    pub ns_kind: NsKind,
    pub target: NodeId,
}

#[derive(Default)]
pub struct ResolvedNames {
    names: NodeMap<ResolvedName>,
}

impl ResolvedNames {
    pub fn insert(&mut self, ns_kind: NsKind, node: NodeId, target: NodeId) {
        assert!(self.names.insert(node, ResolvedName {
            ns_kind,
            target,
        }).is_none());
    }

    pub fn get(&self, node: NodeId) -> &ResolvedName {
        &self.names[&node]
    }
}

pub struct ResolveNames<'a> {
    names: MaintainNameScope<'a>,
    resolved_names: &'a mut ResolvedNames,
    ns_kind_stack: Vec<NsKind>,
}

impl<'a> ResolveNames<'a> {
    pub fn new(names: &'a mut Names, resolved_names: &'a mut ResolvedNames) -> Self {
        Self {
            names: MaintainNameScope { names },
            resolved_names,
            ns_kind_stack: Vec::new(),
        }
    }

    fn push_ns_kind(&mut self, link_kind: NodeLinkKind) {
        use NodeLinkKind::*;
        let ns_kind = match link_kind {
            | BlockExpr
            | BlockFlowCtlValue
            | Cast(CastLink::Expr)
            | FieldAccessReceiver
            | FnCall(_)
            | Fn(FnLink::Body)
            | IfExpr(_)
            | Let(LetLink::Init)
            | LoopBlock
            | Op(_)
            | Range(_)
            | StructValueValue
            | TyExpr(TyExprLink::Array(ArrayLink::Len))
            | While(_)
            => NsKind::Value,

            | Cast(CastLink::Type)
            | Fn(_)
            | FnDeclArgType
            | Impl(_)
            | Let(_)
            | ModuleItem
            | Root
            | StructDecl(_)
            | StructTypeFieldType
            | SymPathTypeArg
            | TyExpr(_)
            | UsePathPath
            | UseStmtPath
            => NsKind::Type,
        };
        self.ns_kind_stack.push(ns_kind);
    }
}

impl AstVisitor for ResolveNames<'_> {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        self.names.before_node(ctx);
    }

    fn node(&mut self, ctx: AstVisitorCtx) {
        self.push_ns_kind(ctx.link_kind);

        match ctx.kind {
            NodeKind::SymPath => {
                let SymPath { anchor, items } = ctx.ast.sym_path(ctx.node);
                if anchor.is_some() {
                    unimplemented!();
                }
                let first = &items[0].ident;
                let ns_kind = *self.ns_kind_stack.last().unwrap();
                if let Some(resolved) = self.names.names.resolve(ns_kind, &first.value) {
                    if items.len() > 1 {
                        unimplemented!();
                    }
                    self.resolved_names.insert(ns_kind, ctx.node, resolved);
                } else {
                    panic!("[{}:{}] couldn't find name `{}` in the current scope",
                        first.span.start, first.span.end, first.value);
                }
            }
            _ => {}
        }
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        self.names.after_node(ctx);
        self.ns_kind_stack.pop().unwrap();
    }
}