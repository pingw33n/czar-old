use enum_as_inner::EnumAsInner;
use enum_map::EnumMap;
use enum_map_derive::Enum;
use std::collections::hash_map::{Entry, HashMap};

use crate::diag::DiagRef;
use crate::hir::*;
use crate::hir::traverse::*;
use crate::util::enums::EnumExt;

use super::FnSignature;

#[derive(EnumAsInner)]
pub enum ScopeItem {
    Single {
        name: S<Ident>,
        node: NodeId,
    },
    Fns(Vec<ScopeFn>),
}

pub struct ScopeFn {
    pub name: S<Ident>,
    pub node: NodeId, // FnDef
}

#[derive(Default)]
pub struct Scope {
    items: HashMap<Ident, ScopeItem>,
    wildcard_imports: Vec<NodeId>,
}

impl Scope {
    fn insert(&mut self, name: S<Ident>, node: NodeId) -> Result<(), ()> {
        match self.items.entry(name.value.clone()) {
            Entry::Occupied(_) => Err(()),
            Entry::Vacant(e) => {
                e.insert(ScopeItem::Single {
                    name,
                    node,
                });
                Ok(())
            },
        }
    }

    fn insert_fn(&mut self,
        name: S<Ident>,
        node: NodeId,
        fn_def_signatures: &NodeMap<FnSignature>,
    ) -> Result<(), ()> {
        match self.items.entry(name.value.clone()) {
            Entry::Occupied(mut e) => {
                if e.get().as_single().is_some() {
                    return Err(());
                }
                match e.get_mut() {
                    ScopeItem::Single { .. } => unreachable!(),
                    ScopeItem::Fns(fns) => {
                        match fns.iter()
                            .position(|s| fn_def_signatures[&s.node] == fn_def_signatures[&node])
                        {
                            Some(_) => Err(()),
                            None => {
                                fns.push(ScopeFn {
                                    name,
                                    node,
                                });
                                Ok(())
                            }
                        }

                    }
                }
            },
            Entry::Vacant(e) => {
                e.insert(ScopeItem::Fns(vec![ScopeFn {
                    name,
                    node,
                }]));
                Ok(())
            },
        }
    }

    pub fn try_get(&self, name: &str) -> Option<&ScopeItem> {
        self.items.get(name)
    }

    pub fn get(&self, name: &str) -> &ScopeItem {
        self.try_get(name).unwrap()
    }

    fn insert_wildcard_import(&mut self, node: NodeId) {
        self.wildcard_imports.push(node);
    }

    pub fn wildcard_imports(&self) -> &[NodeId] {
        &self.wildcard_imports
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty() && self.wildcard_imports.is_empty()
    }
}

#[derive(Clone, Copy, Debug, Enum, Eq, Hash, PartialEq)]
pub enum NsKind {
    Type,
    Value,
}

impl NsKind {
    pub fn other(self) -> Self {
        match self {
            Self::Type => Self::Value,
            Self::Value => Self::Type,
        }
    }
}

#[derive(Default)]
pub struct DiscoverData {
    scopes: NodeMap<EnumMap<NsKind, Scope>>,
    scope_to_parent: NodeMap<NodeId>,
    node_to_scope: NodeMap<NodeId>,
    child_to_parent: NodeMap<NodeId>,
    node_to_module: NodeMap<NodeId>,
    fn_def_signatures: NodeMap<FnSignature>,
}

impl DiscoverData {
    pub fn build(hir: &Hir, diag: DiagRef) -> Self {
        let mut data = Self::default();
        hir.traverse(&mut Build {
            hir,
            data: &mut data,
            in_use: false,
            scope_stack: Vec::new(),
            node_stack: Vec::new(),
            module_stack: Vec::new(),
            diag,
        });
        data
    }

    pub fn scope(&self, scope: NodeId, kind: NsKind) -> &Scope {
        self.try_scope(scope, kind).unwrap()
    }

    pub fn try_scope(&self, scope: NodeId, kind: NsKind) -> Option<&Scope> {
        self.scopes.get(&scope).map(|s| &s[kind])
    }

    fn scope_mut(&mut self, scope: NodeId, kind: NsKind) -> &mut Scope {
        &mut self.scopes.entry(scope)
            .or_insert(Default::default())
            [kind]
    }

    fn insert_fn(&mut self,
        scope: NodeId,
        kind: NsKind,
        name: S<Ident>,
        node: NodeId,
    ) -> Result<(), ()> {
        let scope = &mut self.scopes.entry(scope)
            .or_insert(Default::default())
            [kind];
        match scope.insert_fn(name.clone(), node, &self.fn_def_signatures){
            Ok(()) => Ok(()),
            Err(()) => Err(()),
        }
    }

    pub fn scope_of(&self, node: NodeId) -> NodeId {
        self.node_to_scope[&node]
    }

    fn set_scope_of(&mut self, node: NodeId, scope: NodeId) {
        assert!(self.node_to_scope.insert(node, scope).is_none());
    }

    pub fn try_parent_scope_of(&self, scope: NodeId) -> Option<NodeId> {
        self.scope_to_parent.get(&scope).copied()
    }

    pub fn parent_of(&self, node: NodeId) -> NodeId {
        self.child_to_parent[&node]
    }

    pub fn try_parent_of(&self, node: NodeId) -> Option<NodeId> {
        self.child_to_parent.get(&node).copied()
    }

    pub fn set_parent_of(&mut self, child: NodeId, parent: NodeId) {
        assert!(self.child_to_parent.insert(child, parent).is_none());
    }

    pub fn module_of(&self, node: NodeId) -> NodeId {
        self.node_to_module[&node]
    }

    pub fn try_module_of(&self, node: NodeId) -> Option<NodeId> {
        self.node_to_module.get(&node).copied()
    }

    fn set_module_of(&mut self, node: NodeId, module: NodeId) {
        assert_ne!(node, module);
        assert!(self.node_to_module.insert(node, module).is_none());
    }

    pub fn fn_def_signature(&self, fn_def: NodeId) -> &FnSignature {
        &self.fn_def_signatures[&fn_def]
    }

    pub fn try_fn_def_signature(&self, fn_def: NodeId) -> Option<&FnSignature> {
        self.fn_def_signatures.get(&fn_def)
    }

    pub fn source_of(&self, mut node: NodeId, hir: &Hir) -> SourceId {
        if node == hir.root {
            hir.root_source_id()
        } else {
            loop {
                node = self.module_of(node);
                if let Some(id) = hir.module(node).source_id {
                    break id;
                }
            }
        }
    }

    pub fn print_scopes(&self, hir: &Hir) {
        struct Visitor<'a> {
            data: &'a DiscoverData,
            indent: u32,
        }

        impl Visitor<'_> {
            fn print_indent(&self) {
                for _ in 1..self.indent {
                    print!("  ");
                }
            }
        }

        impl HirVisitor for Visitor<'_> {
            fn before_node(&mut self, ctx: HirVisitorCtx) {
                self.indent += 1;
                self.print_indent();
                let node = ctx.hir.node_kind(ctx.node);
                if let Some(name) = ctx.hir.try_module(ctx.node)
                    .and_then(|Module { name, .. }| name.as_ref())
                {
                    println!("{:?} {:?} `{}` {}:{}",
                        node.value, ctx.node, name.name.value, node.span.start, node.span.end);
                } else {
                    println!("{:?} {:?} {}:{}",
                        node.value, ctx.node, node.span.start, node.span.end);
                }
                for kind in NsKind::iter() {
                    if let Some(scope) = self.data.try_scope(ctx.node, kind) {
                        if !scope.is_empty() {
                            self.print_indent();
                            print!("| {:?}: ", kind);
                            for (i, (ident, scope_item)) in
                                scope.items.iter().enumerate()
                            {
                                if i > 0 {
                                    print!(", ");
                                }
                                match scope_item {
                                    ScopeItem::Single { name, node } => {
                                        let n = ctx.hir.node_kind(*node);
                                        print!("`{}` {}:{} -> {:?} {:?} {}:{}", ident,
                                            name.span.start, name.span.end,
                                            n.value, node, n.span.start, n.span.end);
                                    }
                                    ScopeItem::Fns(fns) => {
                                        for (i, ScopeFn { name, node }) in fns.iter().enumerate() {
                                            let n = ctx.hir.node_kind(*node);
                                            assert_eq!(n.value, NodeKind::FnDef);
                                            if i > 0 {
                                                print!(", ");
                                            }
                                            let key = self.data.fn_def_signature(*node);
                                            print!("`{}::{}` {}:{} -> {:?} {:?} {}:{}",
                                                ident, key,
                                                name.span.start, name.span.end,
                                                n.value, node, n.span.start, n.span.end);
                                        }
                                    }
                                }

                            }
                            println!()
                        }
                    }
                }
            }

            fn after_node(&mut self, _ctx: HirVisitorCtx) {
                self.indent -= 1;
            }
        }

        hir.traverse(&mut Visitor {
            data: self,
            indent: 0,
        });
    }
}

struct Build<'a> {
    hir: &'a Hir,
    data: &'a mut DiscoverData,
    /// Is in `Use` subtree?
    in_use: bool,
    scope_stack: Vec<(ScopeKind, NodeId)>,
    node_stack: Vec<NodeId>,
    module_stack: Vec<NodeId>,
    diag: DiagRef,
}

impl Build<'_> {
    fn find_scope(&self, kind: Option<ScopeKind>) -> NodeId {
        self.scope_stack.iter().copied().rev()
            .find(|&(k, _)| kind.map(|kind| k == kind).unwrap_or(true))
            .map(|(_, n)| n)
            .unwrap()
    }

    fn insert0(&mut self,
        scope_kind: Option<ScopeKind>,
        ns: NsKind,
        name: S<Ident>,
        node: NodeId,
        report_err: bool,
    ) -> Result<(), ()> {
        let scope = self.find_scope(scope_kind);
        if self.data.scope_mut(scope, ns).insert(name.clone(), node).is_err() {
            if report_err {
                self.report_dup_name_error(scope, ns, &name, node);
            }
            Err(())
        } else {
            Ok(())
        }
    }

    fn insert(&mut self, ns: NsKind, name: S<Ident>, node: NodeId, report_err: bool) -> Result<(), ()> {
        self.insert0(Some(ScopeKind::Normal), ns, name, node, report_err)
    }

    fn insert_var(&mut self, ns: NsKind, name: S<Ident>, node: NodeId) {
        let _ = self.insert0(None, ns, name, node, true);
    }

    fn insert_fn(&mut self, ns: NsKind, name: S<Ident>, node: NodeId) {
        let scope = self.find_scope(Some(ScopeKind::Normal));
        if self.data.insert_fn(scope, ns, name.clone(), node).is_ok() {
            return;
        }
        let existing = &self.data.scope(scope, ns).items[&name.value];
        match existing {
            ScopeItem::Single { name, .. } => {
                self.diag.borrow_mut().error_span(self.hir, self.data, node, name.span,
                    format!("function `{}` clashes with other non-function names", name.value));
            }
            ScopeItem::Fns(fns) => {
                self.diag.borrow_mut().error_span(self.hir, self.data, node, name.span,
                    format!("function `{}::{}` is defined multiple times",
                        fns[0].name.value, self.data.fn_def_signature(node)));
            }
        }
    }

    /// Note the `node` is never `FnDef`, that one is handled in `insert_fn()`.
    fn report_dup_name_error(&self, scope: NodeId, ns: NsKind, name: &S<Ident>, node: NodeId) {
        let existing = &self.data.scope(scope, ns).items[&name.value];
        match existing {
            ScopeItem::Single { .. } => {
                self.diag.borrow_mut().error_span(self.hir, self.data, node, name.span,
                    format!("name `{}` is defined multiple times", name.value));
            }
            ScopeItem::Fns(fns) => {
                self.diag.borrow_mut().error_span(self.hir, self.data, node, name.span,
                    format!("name `{}` clashes with identically named function{}",
                        name.value, if fns.len() > 1 { "s" } else { "" }));
            }
        }
    }

    fn insert_all_namespaces(&mut self, name: S<Ident>, node: NodeId) {
        let mut ok = true;
        for ns in NsKind::iter() {
            ok &= self.insert(ns, name.clone(), node, ok).is_ok();
        }
    }

    fn insert_wildcard_import(&mut self, node: NodeId) {
        let scope = self.find_scope(Some(ScopeKind::Normal));
        for ns in NsKind::iter() {
            self.data.scope_mut(scope, ns)
                .insert_wildcard_import(node);
        }
    }
}

impl HirVisitor for Build<'_> {
    fn before_node(&mut self, ctx: HirVisitorCtx) {
        if let Some(&parent) = self.node_stack.last() {
            self.data.set_parent_of(ctx.node, parent);
        }
        if let Some(&module) = self.module_stack.last() {
            self.data.set_module_of(ctx.node, module);
        }
        self.node_stack.push(ctx.node);

        if let Some(&(_, scope)) = self.scope_stack.last() {
            self.data.set_scope_of(ctx.node, scope);
        }

        match ctx.kind {
            NodeKind::FnDef => {
                let name = ctx.hir.fn_def(ctx.node).name.clone();
                let sign = FnSignature::from_def(ctx.node, ctx.hir);
                assert!(self.data.fn_def_signatures.insert(ctx.node, sign).is_none());
                self.insert_fn(NsKind::Value, name, ctx.node);
            },
            NodeKind::FnDefParam => {
                let priv_name = ctx.hir.fn_def_param(ctx.node).priv_name.clone();
                let _ = self.insert(NsKind::Value, priv_name.clone(), ctx.node, true);
            },
            NodeKind::Let => {},
            NodeKind::LetDef => {
                let name = ctx.hir.let_def(ctx.node).name.clone();
                self.insert_var(NsKind::Value, name, ctx.node);
            },
            NodeKind::Module => {
                self.module_stack.push(ctx.node);

                let Module { name, .. } = &ctx.hir.module(ctx.node);
                if let Some(name) = name {
                    let _ = self.insert(NsKind::Type, name.name.clone(), ctx.node, true);
                }
            }
            NodeKind::Struct => {
                let name = ctx.hir.struct_(ctx.node).name.clone();
                let _ = self.insert(NsKind::Type, name, ctx.node, true);
            }
            NodeKind::PathEndIdent if self.in_use => {
                let PathEndIdent {
                    item: PathItem { ident, ty_params: _, .. },
                    renamed_as,
                } = ctx.hir.path_end_ident(ctx.node);
                let name = if ident.value == Ident::self_lower() {
                    let parent = self.data.parent_of(ctx.node);
                    ident.span.spanned(
                        ctx.hir.path_segment(parent).prefix.last().unwrap().ident.value.clone())
                } else {
                    renamed_as.as_ref().unwrap_or(ident).clone()
                };
                self.insert_all_namespaces(name, ctx.node);
            }
            NodeKind::PathEndStar => {
                assert!(self.in_use);
                self.insert_wildcard_import(ctx.node);
            }
            NodeKind::Use => {
                assert!(!self.in_use);
                self.in_use = true;
            }
            | NodeKind::Block
            | NodeKind::BlockFlowCtl
            | NodeKind::Cast
            | NodeKind::FieldAccess
            | NodeKind::FnCall
            | NodeKind::IfExpr
            | NodeKind::Impl
            | NodeKind::Literal
            | NodeKind::Loop
            | NodeKind::Op
            | NodeKind::Path
            | NodeKind::PathEndEmpty
            | NodeKind::PathEndIdent
            | NodeKind::PathSegment
            | NodeKind::Range
            | NodeKind::StructType
            | NodeKind::StructValue
            | NodeKind::StructValueField
            | NodeKind::TyExpr
            | NodeKind::TypeParam
            | NodeKind::While
            => {},
        }

        if let Some(kind) = scope_kind(ctx.kind) {
            self.scope_stack.push((kind, ctx.node));
        }
    }

    fn after_node(&mut self, ctx: HirVisitorCtx) {
        if scope_kind(ctx.kind) == Some(ScopeKind::Normal) {
            loop {
                let (_, scope) = self.scope_stack.pop().unwrap();
                if let Some((_, parent)) = self.scope_stack.last().copied() {
                    self.data.scope_to_parent.insert(scope, parent);
                }
                if scope == ctx.node {
                    break;
                }
            }
        }
        self.node_stack.pop().unwrap();
        if *self.module_stack.last().unwrap() == ctx.node {
            self.module_stack.pop().unwrap();
        }
        match ctx.kind {
            NodeKind::Use => {
                assert!(self.in_use);
                self.in_use = false;
            },
            _ => {},
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ScopeKind {
    Normal,

    /// Scope for variables. Each variable insert its name into parent scope and creates a new
    /// sub-scope of `Var` kind. The `Var` scope lasts as long as the enclosing normal scope.
    ///
    /// For example:
    /// ```
    /// fn f(v: i32) {      // Begin Normal(f), insert `f` into Normal(root)
    ///     S {};           //   Will look up and find `S` in Normal(f)
    ///     let x = 1;      //   Begin Var(x), insert `x` into Normal(f)
    ///     let y = 2;      //     Begin Var(y)#1, insert `y` into Var(x)
    ///     let y = 3;      //       Begin Var(y)#2, insert `y` into Var(y)#1
    ///     f(x + y);       //         Will look up and find `f`, `x`, `y` in scopes starting from Var(y)#2
    ///     struct S {}     //         Insert `S` into Normal(f)
    ///                     //       End Var(y)#2
    ///                     //     End Var(y)#1
    ///                     //   End Var(x)
    /// }                   // End Normal(f)
    /// ```
    Var,
}

fn scope_kind(kind: NodeKind) -> Option<ScopeKind> {
    use NodeKind::*;
    match kind {
        | LetDef
        | Path
        | PathEndEmpty
        | PathEndIdent
        | PathEndStar
        | PathSegment
        | Use
        => None,

        | Block
        | BlockFlowCtl
        | Cast
        | FieldAccess
        | FnCall
        | FnDef
        | FnDefParam
        | IfExpr
        | Impl
        | Literal
        | Loop
        | Module
        | Op
        | Range
        | Struct
        | StructType
        | StructValue
        | StructValueField
        | TyExpr
        | TypeParam
        | While
        => Some(ScopeKind::Normal),

        Let => Some(ScopeKind::Var),
    }
}