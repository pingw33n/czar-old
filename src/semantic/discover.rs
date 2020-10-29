use atomic_refcell::{AtomicRef, AtomicRefCell};
use enum_map::EnumMap;
use enum_map_derive::Enum;
use std::collections::{HashMap, HashSet};

use crate::diag::DiagRef;
use crate::hir::*;
use crate::hir::traverse::*;
use crate::package::GlobalNodeId;
use crate::util::enums::EnumExt;

use super::FnParamsSignature;

/// Item id inside Items::versions. Maps to the index.
pub type ItemId = u32;

#[derive(Default)]
pub struct Items {
    versions: Vec<(ScopeVersion, NodeId)>,

    /// Keeps tracks of items that failed. For import items, multiple nodes will have associated the same id of the
    /// import item.
    failed: AtomicRefCell<HashSet<(ItemId, GlobalNodeId)>>,
}

impl Items {
    pub fn versions(&self) -> &[(ScopeVersion, NodeId)] {
        &self.versions
    }

    pub fn is_failed(&self) -> IsFailedChecker {
        IsFailedChecker(self.failed.borrow())
    }

    pub fn mark_failed(&self, idx: ItemId, node: GlobalNodeId) {
        assert_eq!(self.versions[idx as usize].0, 0);
        self.failed.borrow_mut().insert((idx, node));
    }

    pub fn get(&self, version: ScopeVersion) -> impl Iterator<Item=(ItemId, NodeId)> {
        let mut r = Vec::new(); // FIXME not needed
        let vers = &self.versions;
        let i = match vers.binary_search_by_key(&version, |&(v, _)| v) {
            Ok(i) => Some(i),
            Err(i) => if i > 0 {
                Some(i - 1)
            } else {
                None
            }
        };
        if let Some(mut i) = i {
            // Seek version span start.
            while i > 0 && vers[i - 1].0 == vers[i].0 {
                i -= 1;
            }
            loop {
                r.push((i as ItemId, vers[i].1));
                if vers.get(i + 1).map(|v| v.0) != Some(vers[i].0) {
                    break;
                }
                i += 1;
            }
        }
        r.into_iter()
    }

    fn insert(&mut self, version: Option<&mut ScopeVersion>, node: NodeId) {
        if let Some(version) = version {
            assert!(*version >= self.versions.last().map(|&(v, _)| v).unwrap_or(0));
            *version += 1;
            self.versions.push((*version, node));
        } else {
            let i = self.versions.iter()
                .position(|v| v.0 != 0)
                .unwrap_or(self.versions.len());
            self.versions.insert(i, (0, node));
        }
    }
}

pub struct IsFailedChecker<'a>(AtomicRef<'a, HashSet<(ItemId, GlobalNodeId)>>);

impl IsFailedChecker<'_> {
    pub fn is_failed(&self, id: ItemId, node: GlobalNodeId) -> bool {
        self.0.contains(&(id, node))
    }
}

#[derive(Default)]
pub struct Namespace {
    /// Since the version is shared between all namespaces of a scope, there can be gaps.
    /// Map value is never empty.
    items: HashMap<Ident, Items>,

    /// Names in definition order.
    /// Needed for scope checking so the recursive resolution errors happen deterministically.
    ordered_names: Vec<Ident>,
}

impl Namespace {
    fn insert(&mut self, name: Ident, version: Option<&mut ScopeVersion>, node: NodeId) {
        let def_order = &mut self.ordered_names;
        self.items.entry(name.clone())
            .or_insert_with(|| {
                def_order.push(name);
                Items::default()
            })
            .insert(version, node);
    }

    pub fn ordered_names<'a>(&'a self) -> impl Iterator<Item=&'a Ident> + 'a {
        self.ordered_names.iter()
    }

    pub fn get(&self, name: &str) -> Option<&Items> {
        self.items.get(name)
    }
}

#[derive(Default)]
pub struct Scope {
    /// Node that created this scope, aka `self` in paths.
    node: NodeId,
    version: ScopeVersion,
    namespaces: EnumMap<NsKind, Namespace>,
    wildcard_imports: Vec<NodeId>,
}

impl Scope {
    fn insert(&mut self,
        versioned: bool,
        ns: NsKind,
        name: Ident,
        node: NodeId,
    ) {
        let version = if versioned { Some(&mut self.version) } else { None };
        self.namespaces[ns].insert(name, version, node);
    }

    fn insert_import(&mut self, name: Ident, path: NodeId) {
        for ns in NsKind::iter() {
            self.namespaces[ns].insert(name.clone(), None, path);
        }
    }

    fn insert_wildcard_import(&mut self, node: NodeId) {
        debug_assert!(!self.wildcard_imports.iter().any(|&n| n == node));
        self.wildcard_imports.push(node);
    }

    pub fn namespace(&self, ns: NsKind) -> &Namespace {
        &self.namespaces[ns]
    }

    pub fn namespace_mut(&mut self, ns: NsKind) -> &mut Namespace {
        &mut self.namespaces[ns]
    }

    pub fn wildcard_imports(&self) -> &[NodeId] {
        &self.wildcard_imports
    }
}

#[derive(Clone, Copy, Debug, Enum, Eq, Hash, PartialEq)]
pub enum NsKind {
    Type,
    Value,
}

/// Unversioned scope id. Maps to HIR node that created that scope.
pub type ScopeUid = NodeId;

pub type ScopeVersion = u32;

/// Versioned scope id.
pub type ScopeVid = (ScopeUid, ScopeVersion);

#[derive(Default)]
pub struct DiscoverData {
    scopes: HashMap<ScopeUid, Scope>,
    scope_to_parent: HashMap<ScopeUid, ScopeVid>,
    /// Node to scope where that node is defined.
    node_to_def_scope: NodeMap<ScopeVid>,
    child_to_parent: NodeMap<NodeId>,
    node_to_module: NodeMap<NodeId>,
    fn_def_signatures: NodeMap<FnParamsSignature>,
    impls: Vec<NodeId>,
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

    fn scope_version(&self, uid: ScopeUid) -> ScopeVersion {
        self.scopes.get(&uid).map(|s| s.version).unwrap_or(0)
    }

    pub fn node_of_scope(&self, uid: ScopeUid) -> NodeId {
        self.scopes[&uid].node
    }

    pub fn scopes<'a>(&'a self) -> impl Iterator<Item=(ScopeUid, &'a Scope)> + 'a {
        self.scopes.iter().map(|(k, v)| (*k, v))
    }

    pub fn scope(&self, uid: ScopeUid) -> &Scope {
        self.try_scope(uid).unwrap()
    }

    pub fn scope_mut(&mut self, uid: ScopeUid) -> &mut Scope {
        self.scopes.get_mut(&uid).unwrap()
    }

    pub fn try_scope(&self, uid: ScopeUid) -> Option<&Scope> {
        self.scopes.get(&uid)
    }

    pub fn namespace(&self, uid: ScopeUid, ns: NsKind) -> &Namespace {
        self.try_namespace(uid, ns).unwrap()
    }

    pub fn try_namespace(&self, uid: ScopeUid, ns: NsKind) -> Option<&Namespace> {
        self.try_scope(uid).map(|s| &s.namespaces[ns])
    }

    fn ensure_scope(&mut self, uid: ScopeUid) -> &mut Scope {
        self.scopes.entry(uid)
            .or_insert(Default::default())
    }

    pub fn def_scope_of(&self, node: NodeId) -> ScopeVid {
        self.node_to_def_scope[&node]
    }

    fn set_def_scope_of(&mut self, node: NodeId, uid: ScopeUid) {
        let version = self.scope_version(uid);
        assert!(self.node_to_def_scope.insert(node, (uid, version)).is_none());
    }

    pub fn try_parent_scope_of(&self, uid: ScopeUid) -> Option<ScopeVid> {
        self.scope_to_parent.get(&uid).copied()
    }

    fn set_parent_scope_of(&mut self, uid: ScopeUid, parent: ScopeUid) {
        let version = self.scope_version(parent);
        assert!(self.scope_to_parent.insert(uid, (parent, version)).is_none());
    }

    pub fn parent_of(&self, node: NodeId) -> NodeId {
        self.child_to_parent[&node]
    }

    pub fn try_parent_of(&self, node: NodeId) -> Option<NodeId> {
        self.child_to_parent.get(&node).copied()
    }

    fn set_parent_of(&mut self, child: NodeId, parent: NodeId) {
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

    pub fn fn_def_signature(&self, fn_def: NodeId) -> &FnParamsSignature {
        &self.fn_def_signatures[&fn_def]
    }

    pub fn try_fn_def_signature(&self, fn_def: NodeId) -> Option<&FnParamsSignature> {
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

    pub fn find_path_start(&self, mut node: NodeId, hir: &Hir) -> Option<NodeId> {
        let mut first = true;
        loop {
            match hir.node_kind(node).value {
                NodeKind::Path => break Some(node),
                | NodeKind::PathEndEmpty
                | NodeKind::PathEndIdent
                | NodeKind::PathEndStar
                | NodeKind::PathSegment
                => node = self.parent_of(node),
                _ => {
                    assert!(first);
                    break None;
                }
            }
            first = false;
        }
    }

    pub fn find_fn_call(&self, callee_path: NodeId, hir: &Hir) -> Option<NodeId> {
        let path_head = self.find_path_start(callee_path, hir)?;
        let path_owner = self.parent_of(path_head);
        hir.try_fn_call(path_owner)
            .filter(|f| f.callee == path_head)
            .map(|_| path_owner)
    }

    pub fn find_method_call(&self, callee_path: NodeId, hir: &Hir) -> Option<NodeId> {
        self.find_fn_call(callee_path, hir)
            .filter(|&n| hir.fn_call(n).kind == FnCallKind::Method)
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
                for ns_kind in NsKind::iter() {
                    if let Some(ns) = self.data.try_namespace(ctx.node, ns_kind) {
                        if ns.items.is_empty() {
                            continue;
                        }
                        self.print_indent();
                        print!("| {:?}: ", ns_kind);
                        for (i, (ident, items)) in ns.items.iter().enumerate() {
                            if i > 0 {
                                print!(", ");
                            }
                            for (i, &(ver, node)) in items.versions.iter().enumerate() {
                                if i > 0 {
                                    print!(", ");
                                }
                                let nk = ctx.hir.node_kind(node);
                                let failed = if items.failed.borrow().iter().any(|&(j, _)| j as usize == i) { "(F)" } else { "" };
                                if let Some(sign) = self.data.try_fn_def_signature(node) {
                                    print!("{failed}`{name}::{sign}`#{ver} -> {node_kind:?} {node:?} {s}:{e}",
                                        failed=failed,
                                        name=ident,
                                        sign=sign,
                                        ver=ver,
                                        node_kind= nk.value,
                                        node=node,
                                        s=nk.span.start,
                                        e=nk.span.end);
                                } else {
                                    print!("{failed}`{name}`#{ver} -> {node_kind:?} {node:?} {s}:{e}",
                                        failed=failed,
                                        name=ident,
                                        ver=ver,
                                        node_kind=nk.value,
                                        node=node,
                                        s=nk.span.start,
                                        e=nk.span.end);
                                }
                            }
                        }
                        println!()
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

    pub fn impls(&self) -> &[NodeId] {
        &self.impls
    }

    fn name0(&self, node: NodeId, original: bool, hir: &Hir) -> Option<S<Ident>> {
        // Must be in sync with Self::importable_name()
        Some(match hir.node_kind(node).value {
            NodeKind::FnDef => hir.fn_def(node).name.clone(),
            NodeKind::FnDefParam => hir.fn_def_param(node).name.clone(),
            NodeKind::LetDef => hir.let_def(node).name.clone(),
            NodeKind::Module => hir.module(node).name.as_ref().map(|v| v.name.clone())?,
            NodeKind::Struct => hir.struct_(node).name.clone(),
            NodeKind::TypeParam => hir.type_param(node).name.clone(),
            NodeKind::PathEndIdent => {
                let PathEndIdent {
                    item: PathItem { ident, .. },
                    renamed_as,
                } = hir.path_end_ident(node);
                if ident.value == Ident::self_lower() && (renamed_as.is_none() || original) {
                    let parent = self.parent_of(node);
                    ident.span.spanned(
                        hir.path_segment(parent).prefix.last().unwrap().ident.value.clone())
                } else if !original {
                    renamed_as.as_ref().map(|v| v.clone()).unwrap_or_else(|| ident.clone())
                } else {
                    ident.clone()
                }
            }
            NodeKind::TypeAlias => hir.type_alias(node).name.clone(),

            | NodeKind::Block
            | NodeKind::BlockFlowCtl
            | NodeKind::Cast
            | NodeKind::FieldAccess
            | NodeKind::FnCall
            | NodeKind::IfExpr
            | NodeKind::Impl
            | NodeKind::Let
            | NodeKind::Literal
            | NodeKind::Loop
            | NodeKind::Op
            | NodeKind::Path
            | NodeKind::PathEndEmpty
            | NodeKind::PathEndStar
            | NodeKind::PathSegment
            | NodeKind::Range
            | NodeKind::StructType
            | NodeKind::StructValue
            | NodeKind::StructValueField
            | NodeKind::TyExpr
            | NodeKind::Use
            | NodeKind::While
            => return None,
        })
    }

    pub fn name(&self, node: NodeId, hir: &Hir) -> Option<S<Ident>> {
        self.name0(node, false, hir)
    }

    pub fn original_name(&self, node: NodeId, hir: &Hir) -> Option<S<Ident>> {
        self.name0(node, true, hir)
    }

    pub fn importable_name(&self, node: NodeId, hir: &Hir) -> Option<S<Ident>> {
        match hir.node_kind(node).value {
            NodeKind::PathEndIdent => {
                let maybe_use = self.parent_of(self.find_path_start(node, hir).unwrap());
                if hir.node_kind(maybe_use).value != NodeKind::Use {
                    return None;
                }
                self.name(node, hir)
            }
            // These have name in Self::name()
            | NodeKind::FnDefParam
            | NodeKind::LetDef
            | NodeKind::TypeParam
            => None,

            | NodeKind::FnDef
            | NodeKind::Module
            | NodeKind::Struct
            | NodeKind::Block
            | NodeKind::BlockFlowCtl
            | NodeKind::Cast
            | NodeKind::FieldAccess
            | NodeKind::FnCall
            | NodeKind::IfExpr
            | NodeKind::Impl
            | NodeKind::Let
            | NodeKind::Literal
            | NodeKind::Loop
            | NodeKind::Op
            | NodeKind::Path
            | NodeKind::PathEndEmpty
            | NodeKind::PathEndStar
            | NodeKind::PathSegment
            | NodeKind::Range
            | NodeKind::StructType
            | NodeKind::StructValue
            | NodeKind::StructValueField
            | NodeKind::TyExpr
            | NodeKind::TypeAlias
            | NodeKind::Use
            | NodeKind::While
            => self.name(node, hir),
        }
    }

    pub fn describe_named(&self, node: NodeId, hir: &Hir) -> Option<String> {
        let name = &self.name(node, hir)?.value;
        let kind = match hir.node_kind(node).value {
            NodeKind::FnDef => "function",
            NodeKind::FnDefParam => "function parameter",
            NodeKind::LetDef => "variable",
            NodeKind::Module => "module",
            NodeKind::PathEndIdent => "path",
            NodeKind::Struct => "struct type",
            NodeKind::TypeAlias => "type alias",
            NodeKind::TypeParam => "type parameter",

            | NodeKind::Block
            | NodeKind::BlockFlowCtl
            | NodeKind::Cast
            | NodeKind::FieldAccess
            | NodeKind::FnCall
            | NodeKind::IfExpr
            | NodeKind::Impl
            | NodeKind::Let
            | NodeKind::Literal
            | NodeKind::Loop
            | NodeKind::Op
            | NodeKind::Path
            | NodeKind::PathEndEmpty
            | NodeKind::PathEndStar
            | NodeKind::PathSegment
            | NodeKind::Range
            | NodeKind::StructType
            | NodeKind::StructValue
            | NodeKind::StructValueField
            | NodeKind::TyExpr
            | NodeKind::Use
            | NodeKind::While
            => unreachable!(),
        };
        Some(format!("{} `{}`", kind, name))
    }
}

struct Build<'a> {
    hir: &'a Hir,
    data: &'a mut DiscoverData,
    /// Is in `Use` subtree?
    in_use: bool,
    scope_stack: Vec<ScopeUid>,
    node_stack: Vec<NodeId>,
    module_stack: Vec<NodeId>,
    diag: DiagRef,
}

impl Build<'_> {
    fn cur_scope(&self) -> ScopeUid {
        *self.scope_stack.last().unwrap()
    }

    fn insert_name0(&mut self,
        versioned: bool,
        ns: NsKind,
        name: S<Ident>,
        node: NodeId,
    ) {
        let scope = self.cur_scope();
        self.data.ensure_scope(scope)
            .insert(versioned, ns, name.value.clone(), node);
    }

    fn insert_name(&mut self,
        ns: NsKind,
        name: S<Ident>,
        node: NodeId,
    ) {
        self.insert_name0(false, ns, name, node);
    }

    fn insert_versioned_name(&mut self,
        ns: NsKind,
        name: S<Ident>,
        node: NodeId,
    ) {
        self.insert_name0(true, ns, name, node);
    }

    fn insert_import(&mut self, name: S<Ident>, node: NodeId) {
        let scope = self.cur_scope();
        self.data.ensure_scope(scope).insert_import(name.value.clone(), node);
    }

    fn insert_wildcard_import(&mut self, node: NodeId) {
        let scope = self.cur_scope();
        self.data.ensure_scope(scope).insert_wildcard_import(node);
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

        if let Some(&uid) = self.scope_stack.last() {
            self.data.set_def_scope_of(ctx.node, uid);
        }

        match ctx.kind {
            NodeKind::FnDef => {
                let sign = FnParamsSignature::from_def(ctx.node, ctx.hir);
                assert!(self.data.fn_def_signatures.insert(ctx.node, sign).is_none());
            }
            NodeKind::Module => {
                self.module_stack.push(ctx.node);
            }
            NodeKind::PathEndStar => {
                assert!(self.in_use);
                self.insert_wildcard_import(ctx.node);
            }
            NodeKind::Use => {
                assert!(!self.in_use);
                self.in_use = true;
            }
            _ => {}
        }
        if let Some(name) = self.data.importable_name(ctx.node, self.hir) {
            match ctx.kind {
                NodeKind::FnDef => {
                    if !matches!(ctx.link, NodeLink::Impl(_)) {
                        self.insert_name(NsKind::Value, name, ctx.node);
                    }
                }
                NodeKind::Module => {
                    self.insert_name(NsKind::Type, name, ctx.node);
                }
                NodeKind::Struct => {
                    self.insert_name(NsKind::Type, name, ctx.node);
                }
                NodeKind::PathEndIdent if self.in_use => {
                    self.insert_import(name, ctx.node);
                }
                NodeKind::TypeAlias => {
                    self.insert_name(NsKind::Type, name, ctx.node);
                }
                _ => {},
            }
        }

        if creates_scope(ctx.kind) {
            if let Some(&uid) = self.scope_stack.last() {
                self.data.set_parent_scope_of(ctx.node, uid);
            }
            self.scope_stack.push(ctx.node);
        }

        match ctx.kind {
            NodeKind::FnDef => {
                let params = &ctx.hir.fn_def(ctx.node).params;
                for &param in params {
                    let name = ctx.hir.fn_def_param(param).name.clone();
                    self.insert_name(NsKind::Value, name.clone(), param);
                }
            }
            NodeKind::Impl => {
                let for_ = ctx.hir.impl_(ctx.node).for_;
                let for_path_end = ctx.hir.find_flat_path_end(for_);
                let span = ctx.hir.node_kind(for_).span;
                self.insert_import(span.spanned(Ident::self_upper()), for_path_end);
                self.data.impls.push(ctx.node);
            }
            _ => {}
        }
    }

    fn after_node(&mut self, ctx: HirVisitorCtx) {
        self.node_stack.pop().unwrap();
        if *self.module_stack.last().unwrap() == ctx.node {
            self.module_stack.pop().unwrap();
        }

        if creates_scope(ctx.kind) {
            assert_eq!(self.scope_stack.pop().unwrap(), ctx.node);
        }
        match ctx.kind {
            NodeKind::LetDef => {
                let name = ctx.hir.let_def(ctx.node).name.clone();
                self.insert_versioned_name(NsKind::Value, name, ctx.node);
            },
            NodeKind::Use => {
                assert!(self.in_use);
                self.in_use = false;
            },
            _ => {},
        }
    }
}

fn creates_scope(kind: NodeKind) -> bool {
    use NodeKind::*;
    match kind {
        | Block
        | FnDef
        | Impl
        | Module
        => true,

        | BlockFlowCtl
        | Cast
        | FieldAccess
        | FnCall
        | FnDefParam
        | IfExpr
        | Let
        | LetDef
        | Literal
        | Loop
        | Op
        | Path
        | PathEndEmpty
        | PathEndIdent
        | PathEndStar
        | PathSegment
        | Range
        | Struct
        | StructType
        | StructValue
        | StructValueField
        | TyExpr
        | TypeAlias
        | TypeParam
        | Use
        | While
        => false,
    }
}