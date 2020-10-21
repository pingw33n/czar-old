use enum_map::EnumMap;
use enum_map_derive::Enum;
use if_chain::if_chain;
use std::collections::hash_map::{Entry, HashMap};

use crate::diag::DiagRef;
use crate::hir::*;
use crate::hir::traverse::*;
use crate::util::enums::EnumExt;

use super::FnSignature;

#[derive(Clone, Copy, Debug)]
enum ScopeItemKind {
    /// Item doesn't increment the version on insert, thus all forward items are available at version 0.
    /// Duplicate names is failure.
    Forward,

    /// Item increments the version before insert, thus progressive item start at version 1.
    /// Shadows any existing items of any kind.
    Progressive,
}

enum ScopeItem {
    // TODO optimize for no overloads case
    Fns(Vec<NodeId>), // FnDefs
    Single(NodeId),
}

#[derive(Default)]
pub struct Scope {
    items: HashMap<Ident, Vec<(ScopeVersion, ScopeItem)>>, // TODO optimize for single version case
    wildcard_imports: Vec<NodeId>,
}

impl Scope {
    fn insert(&mut self,
        kind: ScopeItemKind,
        name: S<Ident>,
        version: &mut ScopeVersion,
        node: NodeId,
        fn_def_signatures: &NodeMap<FnSignature>,
    ) -> Result<(), ()> {
        let new_item = || if fn_def_signatures.contains_key(&node) {
                ScopeItem::Fns(vec![node])
            } else {
                ScopeItem::Single(node)
            };
        match self.items.entry(name.value.clone()) {
            Entry::Occupied(mut e) => {
                assert!(e.get().len() > 0);
                match kind {
                    ScopeItemKind::Forward => {
                        if e.get().len() == 1 {
                            if let ScopeItem::Fns(fns) = &mut e.get_mut()[0].1 {
                                // TODO: maybe optimize this linear search
                                if_chain! {
                                    if let Some(new_sign) = fn_def_signatures.get(&node);
                                    if fns.iter().all(|n| &fn_def_signatures[n] != new_sign);
                                    then {
                                        fns.push(node);
                                        Ok(())
                                    } else {
                                        Err(())
                                    }
                                }
                            } else {
                                Err(())
                            }
                        } else {
                            debug_assert!(e.get().iter().all(|(_, i)| matches!(i, ScopeItem::Single(_))));
                            Err(())
                        }
                    }
                    ScopeItemKind::Progressive => {
                        assert!(*version >= e.get().last().map(|&(v, _)| v).unwrap_or(0));
                        *version += 1;
                        let item = new_item();
                        e.get_mut().push((*version, item));
                        Ok(())
                    }
                }
            }
            Entry::Vacant(e) => {
                let item = new_item();
                let version = match kind {
                    ScopeItemKind::Forward => 0,
                    ScopeItemKind::Progressive => {
                        *version += 1;
                        *version
                    }
                };
                e.insert(vec![(version, item)]);
                Ok(())
            }
        }
    }

    pub fn get<'a>(&'a self, name: &str, version: ScopeVersion) -> impl Iterator<Item=NodeId> + 'a {
        let mut r = Vec::new();
        if let Some(items) = self.items.get(name) {
            let i = match items.binary_search_by_key(&version, |&(v, _)| v) {
                Ok(i) => Some(i),
                Err(i) => if i > 0 {
                    Some(i - 1)
                } else {
                    None
                }
            };
            if let Some(i) = i {
                match &items[i].1 {
                    ScopeItem::Fns(nodes) => r.extend_from_slice(nodes),
                    &ScopeItem::Single(node) => r.push(node),
                }
            }
        }
        r.into_iter()
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

#[derive(Default)]
struct NsScopes {
    /// Node that created this scope, aka `self` in paths.
    node: NodeId,
    version: ScopeVersion,
    scopes: EnumMap<NsKind, Scope>,
}

impl NsScopes {
    fn insert(&mut self,
        kind: ScopeItemKind,
        ns: NsKind,
        name: S<Ident>,
        node: NodeId,
        fn_def_signatures: &NodeMap<FnSignature>,
    ) -> Result<(), ()> {
        self.scopes[ns].insert(kind, name, &mut self.version, node, fn_def_signatures)
    }
}

#[derive(Clone, Copy, Debug, Enum, Eq, Hash, PartialEq)]
pub enum NsKind {
    Type,
    Value,
}

pub type ScopeUid = NodeId;
pub type ScopeVersion = u32;
pub type ScopeVid = (ScopeUid, ScopeVersion);

#[derive(Default)]
pub struct DiscoverData {
    scopes: HashMap<ScopeUid, NsScopes>,
    scope_to_parent: HashMap<ScopeUid, ScopeVid>,
    /// Node to scope where that node is defined.
    node_to_def_scope: NodeMap<ScopeVid>,
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

    fn scope_version(&self, uid: ScopeUid) -> ScopeVersion {
        self.scopes.get(&uid).map(|s| s.version).unwrap_or(0)
    }

    pub fn node_of_scope(&self, uid: ScopeUid) -> NodeId {
        self.scopes[&uid].node
    }

    pub fn scope(&self, uid: ScopeUid, ns: NsKind) -> &Scope {
        self.try_scope(uid, ns).unwrap()
    }

    pub fn try_scope(&self, uid: ScopeUid, ns: NsKind) -> Option<&Scope> {
        self.scopes.get(&uid).map(|s| &s.scopes[ns])
    }

    fn ensure_scope(&mut self, uid: ScopeUid, ns: NsKind) -> &mut Scope {
        &mut self.scopes.entry(uid)
            .or_insert(Default::default())
            .scopes[ns]
    }

    fn insert_name(&mut self,
        kind: ScopeItemKind,
        ns: NsKind,
        scope: ScopeUid,
        name: S<Ident>,
        node: NodeId,
    ) -> Result<(), ()> {
        let scope = self.scopes.entry(scope)
            .or_insert(Default::default());
        scope.insert(kind, ns, name.clone(), node, &self.fn_def_signatures)
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
                        if scope.is_empty() {
                            continue;
                        }
                        self.print_indent();
                        print!("| {:?}: ", kind);
                        for (ident, items) in &scope.items {
                            for (i, (ver, item)) in items.iter().enumerate() {
                                if i > 0 {
                                    print!(", ");
                                }
                                match &item {
                                    ScopeItem::Single(node) => {
                                        let n = ctx.hir.node_kind(*node);
                                        print!("`{name}`#{ver} -> {node_kind:?} {node:?} {s}:{e}",
                                            name=ident,
                                            ver=ver,
                                            node_kind=n.value,
                                            node=node,
                                            s=n.span.start,
                                            e=n.span.end);
                                    }
                                    ScopeItem::Fns(fns) => {
                                        for (i, &node) in fns.iter().enumerate() {
                                            let n = ctx.hir.node_kind(node);
                                            assert_eq!(n.value, NodeKind::FnDef);
                                            if i > 0 {
                                                print!(", ");
                                            }
                                            let sign = self.data.fn_def_signature(node);
                                            print!("`{name}::{sign}`#{ver} -> {node_kind:?} {node:?} {s}:{e}",
                                                name=ident,
                                                sign=sign,
                                                ver=ver,
                                                node_kind=n.value,
                                                node=node,
                                                s=n.span.start,
                                                e=n.span.end);
                                        }
                                    }
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
        kind: ScopeItemKind,
        ns: NsKind,
        name: S<Ident>,
        node: NodeId,
        report_err: bool,
    ) -> Result<(), ()> {
        let scope = self.cur_scope();
        if self.data.insert_name(kind, ns, scope, name.clone(), node).is_err() {
            if report_err {
                self.report_dup_name_error(scope, ns, &name, node);
            }
            Err(())
        } else {
            Ok(())
        }
    }

    fn insert_name(&mut self,
        kind: ScopeItemKind,
        ns: NsKind,
        name: S<Ident>,
        node: NodeId,
    ) {
        let _ = self.insert_name0(kind, ns, name, node, true);
    }

    fn report_dup_name_error(&self, scope: ScopeUid, ns: NsKind, name: &S<Ident>, node: NodeId) {
        let existing = &self.data.scope(scope, ns).items[&name.value].last().unwrap().1;
        if let Some(fn_sign) = self.data.try_fn_def_signature(node) {
            match existing {
                ScopeItem::Fns(_) => {
                    self.diag.borrow_mut().error_span(self.hir, self.data, node, name.span,
                        format!("function `{}::{}` is defined multiple times",
                            name.value, fn_sign));
                }
                ScopeItem::Single(_) => {
                    self.diag.borrow_mut().error_span(self.hir, self.data, node, name.span,
                        format!("function `{}::{}` clashes with other non-function names",
                            name.value, fn_sign));
                }
            }
        } else {
            match existing {
                ScopeItem::Fns(fns) => {
                    self.diag.borrow_mut().error_span(self.hir, self.data, node, name.span,
                        format!("name `{}` clashes with identically named function{}",
                            name.value, if fns.len() > 1 { "s" } else { "" }));
                }
                ScopeItem::Single(_) => {
                    self.diag.borrow_mut().error_span(self.hir, self.data, node, name.span,
                        format!("name `{}` is defined multiple times", name.value));
                }
            }
        }
    }

    fn insert_name_all(&mut self,
        kind: ScopeItemKind,
        name: S<Ident>,
        node: NodeId,
    ) {
        let mut ok = true;
        for ns in NsKind::iter() {
            ok &= self.insert_name0(kind, ns, name.clone(), node, ok).is_ok();
        }
    }

    fn insert_wildcard_import(&mut self, node: NodeId) {
        let scope = self.cur_scope();
        for ns in NsKind::iter() {
            self.data.ensure_scope(scope, ns)
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

        if let Some(&uid) = self.scope_stack.last() {
            self.data.set_def_scope_of(ctx.node, uid);
        }

        match ctx.kind {
            NodeKind::FnDef => {
                let name = ctx.hir.fn_def(ctx.node).name.clone();
                let sign = FnSignature::from_def(ctx.node, ctx.hir);
                assert!(self.data.fn_def_signatures.insert(ctx.node, sign).is_none());
                self.insert_name(ScopeItemKind::Forward, NsKind::Value, name, ctx.node);
            },
            NodeKind::Module => {
                self.module_stack.push(ctx.node);

                let name = &ctx.hir.module(ctx.node).name;
                if let Some(name) = name {
                    self.insert_name(ScopeItemKind::Forward, NsKind::Type, name.name.clone(), ctx.node);
                }
            }
            NodeKind::Struct => {
                let name = ctx.hir.struct_(ctx.node).name.clone();
                self.insert_name(ScopeItemKind::Forward, NsKind::Type, name, ctx.node);
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
                self.insert_name_all(ScopeItemKind::Forward, name, ctx.node);
            }
            NodeKind::PathEndStar => {
                assert!(self.in_use);
                self.insert_wildcard_import(ctx.node);
            }
            NodeKind::Use => {
                assert!(!self.in_use);
                self.in_use = true;
            }
            _ => {},
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
                    let priv_name = ctx.hir.fn_def_param(param).priv_name.clone();
                    self.insert_name(ScopeItemKind::Forward, NsKind::Value, priv_name.clone(), param);
                }
            }
            _ => {}
        }
    }

    fn after_node(&mut self, ctx: HirVisitorCtx) {
        if creates_scope(ctx.kind) {
            assert_eq!(self.scope_stack.pop().unwrap(), ctx.node);
        }
        self.node_stack.pop().unwrap();
        if *self.module_stack.last().unwrap() == ctx.node {
            self.module_stack.pop().unwrap();
        }
        match ctx.kind {
            NodeKind::LetDef => {
                let name = ctx.hir.let_def(ctx.node).name.clone();
                self.insert_name(ScopeItemKind::Progressive, NsKind::Value, name, ctx.node);
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
        | TypeParam
        | Use
        | While
        => false,
    }
}