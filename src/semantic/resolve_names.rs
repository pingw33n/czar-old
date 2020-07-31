use crate::syntax::*;
use crate::syntax::traverse::*;
use super::discover_names::{AstScopeStack, Names, NsKind};

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
    stack: AstScopeStack,
    names: &'a mut Names,
    resolved_names: &'a mut ResolvedNames,
    ns_kind_stack: Vec<NsKind>,
}

impl<'a> ResolveNames<'a> {
    pub fn new(names: &'a mut Names, resolved_names: &'a mut ResolvedNames) -> Self {
        Self {
            stack: AstScopeStack::new(),
            names,
            resolved_names,
            ns_kind_stack: Vec::new(),
        }
    }

    fn ns_kind(link_kind: NodeLinkKind) -> Option<NsKind> {
        use NodeLinkKind::*;
        Some(match link_kind {
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
            | Fn(FnLink::TypeArg)
            | Fn(FnLink::RetType)
            | FnDeclArgType
            | Impl(ImplLink::TypeArg)
            | Let(LetLink::Type)
            | Path(PathLink::EndIdentTyArgs)
            | Path(PathLink::SegmentItemTyArgs)
            | StructDecl(_)
            | StructTypeFieldType
            | TyExpr(_)
            | UseStmtPath
            => NsKind::Type,

            | Fn(_)
            | Impl(_)
            | Let(_)
            | ModuleItem
            | Path(_)
            | Root
            => return None,
        })
    }

    fn push_ns_kind(&mut self, link_kind: NodeLinkKind) {
        if let Some(v) = Self::ns_kind(link_kind) {
            self.ns_kind_stack.push(v);
        }
    }
}

impl AstVisitor for ResolveNames<'_> {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        self.stack.before_node(ctx);
    }

    fn node(&mut self, ctx: AstVisitorCtx) {
        self.push_ns_kind(ctx.link_kind);

        match ctx.kind {
            NodeKind::Path => {
                let Path { anchor, segment } = ctx.ast.path(ctx.node);
                if anchor.is_some() {
                    unimplemented!();
                }
                let PathSegment { prefix, suffix } = ctx.ast.path_segment(*segment);
                if prefix.len() > 0 || suffix.len() > 1 || ctx.ast.node_kind(suffix[0]).value != NodeKind::PathEndIdent {
                    unimplemented!();
                }
                let PathEndIdent { item, renamed_as } = ctx.ast.path_end_ident(suffix[0]);
                if renamed_as.is_some() {
                    unimplemented!();
                }
                let ns_kind = *self.ns_kind_stack.last().unwrap();
                if let Some(resolved) = self.names.resolve(&self.stack, ns_kind, &item.ident.value) {
                    self.resolved_names.insert(ns_kind, suffix[0], resolved);
                } else {
                    panic!("[{}:{}] couldn't find name `{}` in the current scope",
                        item.ident.span.start, item.ident.span.end, item.ident.value);
                }
            }
            _ => {}
        }
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        self.stack.after_node(ctx);
        if let Some(v) = Self::ns_kind(ctx.link_kind) {
            assert_eq!(self.ns_kind_stack.pop().unwrap(), v);
        }
    }
}