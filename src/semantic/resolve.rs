use atomic_refcell::AtomicRefCell;
use enum_as_inner::EnumAsInner;
use enum_map::EnumMap;
use if_chain::if_chain;
use std::collections::HashSet;

use crate::diag::DiagRef;
use crate::hir::*;
use crate::package::{GlobalNodeId, PackageId, Packages};
use crate::util::enums::EnumExt;
use crate::util::iter::IteratorExt;

use super::PathItem;
use super::discover::{DiscoverData, NsKind, ScopeVid};

#[derive(Default)]
pub struct ResolveData {
    inner: AtomicRefCell<ResolveDataInner>,
}

#[derive(Default)]
struct ResolveDataInner {
    /// Resolution result cache.
    resolutions: NodeMap<Result<Resolution>>,

    /// Dedups errors in tree paths.
    /// This is needed because not all errors can be cached: e.g. items in `PathSegment`.
    errors: HashSet<(SourceId, Span)>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResolutionKind {
    Exact,

    /// `nodes` consist of module node to which the empty path points.
    /// `type_path` path is empty.
    Empty,

    /// `nodes` consist of module node to which the wildcard path points.
    /// `type_path` path is empty.
    Wildcard,

    /// Nodes consist of type node starting from which type-based resolution is required.
    /// `type_path` is the path starting at the type node.
    Type,
}

#[derive(Clone, Debug)]
pub struct Resolution {
    kind: ResolutionKind,
    nodes: EnumMap<NsKind, Vec<GlobalNodeId>>,
    /// See `ResolutionKind` for details.
    type_path: Vec<PathItem>,
}

impl Resolution {
    fn new(kind: ResolutionKind) -> Self {
        Self {
            kind,
            nodes: Default::default(),
            type_path: Default::default(),
        }
    }

    pub fn kind(&self) -> ResolutionKind {
        self.kind
    }

    pub fn nodes<'a>(&'a self) -> impl Iterator<Item=(NsKind, GlobalNodeId)> + 'a {
        let mut r = Vec::new();
        for (ns, n) in &self.nodes {
            for &n in n {
                r.push((ns, n));
            }
        }
        r.into_iter()
    }

    pub fn ns_nodes<'a>(&'a self, ns: NsKind) -> impl Iterator<Item=GlobalNodeId> + 'a {
        self.nodes[ns].iter().copied()
    }

    pub fn ns_nodes_slice(&self, ns: NsKind) -> &[GlobalNodeId] {
        &self.nodes[ns]
    }

    pub fn is_full(&self) -> bool {
        for ns in NsKind::iter() {
            if self.nodes[ns].is_empty() {
                return false;
            }
        }
        true
    }

    fn insert(&mut self, ns: NsKind, node: GlobalNodeId) {
        self.nodes[ns].push(node);
    }

    fn type_or_value(&self) -> Option<GlobalNodeId> {
        self.ns_nodes(NsKind::Type).next()
            .or_else(|| self.ns_nodes(NsKind::Value).next())
    }

    fn clear(&mut self) {
        for vec in self.nodes.values_mut() {
            vec.clear();
        }
        self.type_path.clear();
    }

    pub fn len(&self) -> usize {
        self.nodes.values()
            .map(|v| v.len())
            .sum()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn type_path(&self) -> &[PathItem] {
        &self.type_path
    }
}

pub type Result<T> = std::result::Result<T, ()>;

pub struct ResolveImports<'a> {
    pub discover_data: &'a DiscoverData,
    pub hir: &'a Hir,
    pub resolve_data: &'a ResolveData,
    pub package_id: PackageId,
    pub packages: &'a Packages,
    pub diag: DiagRef<'a>,
}

impl ResolveImports<'_> {
    /// This pass goes over all scopes and verifies there are no conflicts between defined and imported names.
    /// Marks the failed items via `Items::mark_failed()` for the resolver to use.
    /// Non-defining imports like wildcards, are expected to be checked later.
    pub fn run(&mut self) {
        let resolver = Resolver {
            hir: self.hir,
            discover_data: &*self.discover_data,
            resolve_data: self.resolve_data,
            package_id: self.package_id,
            packages: self.packages,
            diag: self.diag,
        };
        let nodes = &mut Vec::new();
        for (_, scope) in self.discover_data.scopes() {
            for ns_kind in NsKind::iter() {
                let ns = scope.namespace(ns_kind);
                for name in ns.ordered_names() {
                    let items = ns.get(name).unwrap();
                    nodes.clear();
                    for (i, &(ver, node)) in items.versions().iter().enumerate() {
                        if ver != 0 {
                            break;
                        }
                        if self.hir.node_kind(node).value == NodeKind::PathEndIdent {
                            if let Ok(reso) = resolver.resolve_node(node) {
                                if reso.kind() == ResolutionKind::Exact {
                                    let mut failed = false;
                                    for target_node in reso.ns_nodes(ns_kind) {
                                        // Note due to recursive resolution we can be getting duplicate target_node's here.
                                        if !failed && self.insert(nodes, node, target_node).is_err() {
                                            failed = true;
                                        }
                                        if failed {
                                            items.mark_failed(i as u32, target_node);
                                        }
                                    }
                                }
                            }
                        } else {
                            let target_node = (self.package_id, node);
                            if self.insert(nodes, node, target_node).is_err() {
                                items.mark_failed(i as u32, target_node);
                            }
                        }
                    }
                }
            }
        }
    }

    fn insert(&self,
        nodes: &mut Vec<(GlobalNodeId, Option<NodeId>)>,
        name_node: NodeId,
        node: GlobalNodeId,
    ) -> Result<()> {
        let name = || self.discover_data.name(name_node, self.hir).unwrap();
        let original_name = || self.discover_data.original_name(name_node, self.hir).unwrap();

        let hir = |pkg| if node.0 == self.package_id {
            self.hir
        } else {
            &self.packages[pkg].hir
        };
        let disc_data = |pkg| if node.0 == self.package_id {
            &*self.discover_data
        } else {
            &self.packages[pkg].discover_data
        };

        debug_assert!(disc_data(node.0).name(node.1, hir(node.0)).is_some());
        debug_assert_ne!(hir(node.0).node_kind(node.1).value, NodeKind::PathEndIdent);

        let import_name_node = if self.discover_data.find_use_node(name_node, self.hir).is_some() {
            Some(name_node)
        } else {
            None
        };

        if import_name_node.is_some()
            && disc_data(node.0).importable_name(node.1, hir(node.0)).is_none()
        {
            let span = original_name().span;
            let name = disc_data(node.0).describe_named(node.1, hir(node.0)).unwrap();
            self.error(name_node, span, format!("{} can't be imported", name));
            return Err(());
        }

        let fn_sign = disc_data(node.0).try_fn_def_signature(node.1);
        let mut had_fn_import = None;
        for &(existing, existing_import_nn) in &*nodes {
            let existing_fn_sign = disc_data(existing.0).try_fn_def_signature(existing.1);
            let ok = if let Some(fn_sign) = fn_sign {
                if let Some(existing_fn_sign) = existing_fn_sign {
                    // New fn vs existing fn.

                    if import_name_node.is_some()
                        && import_name_node != existing_import_nn
                        && existing != node
                    {
                        // Importing a fn: check if it's the same import.
                        let name = name();
                        let original_name = original_name();
                        if name == original_name {
                            self.error(name_node, name.span, format!(
                                "can't import function `{}`: there are conflicting overloads",
                                name.value));
                        } else {
                            self.error(name_node, name.span, format!(
                                "can't import function `{}` as `{}`: there are conflicting overloads",
                                original_name.value, name.value));
                        }
                        false
                    } else if import_name_node.is_none() && existing_import_nn.is_some() {
                        // Defining a fn: check there are no fn imports.
                        let name = name();
                        self.error(name_node, name.span, format!(
                            "can't define function `{}`: there are conflicting overloads",
                            name.value));
                        false
                    } else if existing_fn_sign == fn_sign {
                        let name = name();
                        self.error(name_node, name.span, format!(
                            "function `{}` is defined multiple times",
                                fn_sign.display_with_name(&name.value)));
                        false
                    } else {
                        true
                    }
                } else {
                    // New fn vs existing non-fn.
                    let name = name();
                    self.error(name_node, name.span, format!(
                        "function `{}::{}` redefines already defined name",
                            name.value, fn_sign));
                    false
                }
            } else if let Some(_existing_fn_sign) = existing_fn_sign {
                // New non-fn vs existing fn.
                let name = name();
                self.error(name_node, name.span, format!(
                    "name `{}` redefines already defined function",
                        name.value));
                false
            } else {
                // New non-fn vs existing non-fn.
                let name = name();
                self.error(name_node, name.span, format!(
                    "name `{}` is defined multiple times",
                        name.value));
                false
            };
            if !ok {
                return Err(());
            }
            if existing_fn_sign.is_some() {
                let ex = had_fn_import.replace(existing_import_nn);
                assert!(ex.is_none() || ex == had_fn_import);
            }
        }
        nodes.push((node, import_name_node));
        Ok(())
    }

    fn error(&self, node: NodeId, span: Span, text: String) {
        self.diag.borrow_mut().error_span(self.hir, self.discover_data, node, span, text);
    }
}

#[derive(Debug, EnumAsInner)]
enum PathItem2 {
    Ident(Ident),
    PathItem(PathItem),
    End(Span),
}

impl PathItem2 {
    fn name(&self) -> Spanned<Option<&Ident>> {
        match self {
            Self::Ident(v) => Span::empty().spanned(Some(v)),
            Self::PathItem(v) => v.name.as_ref().map(Some),
            &Self::End(span) => span.spanned(None),
        }
    }
}

#[derive(Clone)]
pub struct Resolver<'a> {
    pub hir: &'a Hir,
    pub discover_data: &'a DiscoverData,
    pub resolve_data: &'a ResolveData,
    pub package_id: PackageId,
    pub packages: &'a Packages,
    pub diag: DiagRef<'a>,
}

impl Resolver<'_> {
    pub fn resolve_node(&self, path: NodeId) -> Result<Resolution> {
        self.resolve(path, &mut HashSet::new())
    }

    pub fn resolve_in_package(&self,
        path: &[&str],
    ) -> Result<Resolution> {
        let path_items: Vec<_> = path
            .iter()
            .map(|&s| PathItem2::Ident(Ident::from(s)))
            .collect();
        let mut reso = Resolution::new(ResolutionKind::Exact);
        self.clone().resolve_path_items(
            &mut reso,
            self.hir.root,
            (self.hir.root, 0),
            Some(&PathAnchor::Package { name: None }),
            path_items,
            &mut HashSet::new(),
        )?;
        Ok(reso)
    }

    fn with_package(&self, package_id: PackageId) -> Self {
        if package_id == self.package_id {
            self.clone()
        } else {
            let package = &self.packages[package_id];
            Self {
                discover_data: &package.discover_data,
                hir: &package.hir,
                package_id,
                packages: self.packages,
                diag: self.diag,
                resolve_data: &package.resolve_data,
            }
        }
    }

    fn hir(&self, package_id: PackageId) -> &Hir {
        if package_id == self.package_id {
            self.hir
        } else {
            &self.packages[package_id].hir
        }
    }

    fn reso_kind(&self, path: NodeId) -> ResolutionKind {
        match self.hir.node_kind(path).value {
            NodeKind::PathEndIdent => ResolutionKind::Exact,
            NodeKind::PathEndStar => ResolutionKind::Wildcard,
            NodeKind::PathEndEmpty => ResolutionKind::Empty,
            _ => unreachable!(),
        }
    }

    fn resolve(&self,
        path: NodeId,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<Resolution> {
        if let Some(r) = self.resolve_data.inner.borrow().resolutions.get(&path) {
            return r.clone();
        }

        let mut reso = Resolution::new(self.reso_kind(path));

        if !paths.insert((self.package_id, path)) {
            return Ok(reso);
        }

        let anchor = self.hir.path(self.discover_data.find_path_start(path, self.hir).unwrap()).anchor
            .as_ref().map(|v| v.as_ref());
        let path_items = self.make_path_items(path);
        let r = self.resolve0(&mut reso, path, anchor, path_items, paths);

        assert!(paths.remove(&(self.package_id, path)));

        if self.discover_data.find_use_node(path, self.hir).is_some() {
            assert!(self.resolve_data.inner.borrow_mut().resolutions.insert(path, r.map(|_| reso.clone())).is_none());
        }

        r?;

        Ok(reso)
    }

    fn make_path_items(&self, path: NodeId) -> Vec<PathItem2> {
        let path_items = PathItem::from_hir_path_end(path, self.hir, self.discover_data);
        let mut r = path_items.into_iter()
            .map(PathItem2::PathItem)
            .collect::<Vec<_>>();
        let nk = self.hir.node_kind(path);
        if matches!(nk.value, NodeKind::PathEndStar | NodeKind::PathEndEmpty) {
            r.push(PathItem2::End(nk.span));
        }
        r
    }

    fn resolve0(&self,
        reso: &mut Resolution,
        path: NodeId,
        anchor: Option<S<&PathAnchor>>,
        path_items: Vec<PathItem2>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<()> {
        let initial_kind = reso.kind();
        assert!(reso.is_empty());
        if let Some(anchor) = anchor {
            let node = match anchor.value {
                PathAnchor::Package { name } => {
                    if let Some(name) = name {
                        if let Some(pkg) = self.packages.try_by_name(&name.value) {
                            (pkg.id, pkg.hir.root)
                        } else {
                            self.error(path, name.span, format!(
                                "can't resolve path: package `{}` not found", name.value));
                            return Err(());
                        }
                    } else {
                        (self.package_id, self.hir.root)
                    }
                }
                &PathAnchor::Super { count } => {
                    assert!(count > 0);
                    let mut scope = path;
                    for _ in 0..=count {
                        scope = if let Some(scope) = self.discover_data.try_module_of(scope) {
                            scope
                        } else {
                            self.error(path, anchor.span,
                                "can't resolve path: too many leading `super` keywords".into());
                            return Err(());
                        };
                    }
                    (self.package_id, scope)
                }
            };
            reso.insert(NsKind::Type, node);
        } else {
            let scope = self.discover_data.def_scope_of(path);
            let first = path_items.first().unwrap().name();
            let first = first.map(|v| v.unwrap());
            self.resolve_in_scope_tree(reso, path, scope, first, paths)?;
            if !reso.is_empty() {
            } else if let Some(package) = self.packages.try_by_name(&first.value) {
                reso.insert(NsKind::Type, (package.id, package.hir.root));
            } else {
                let std_resolver = self.with_package(PackageId::std());
                // TODO cache this
                let std_prelude = std_resolver
                    .resolve_in_package(&["prelude"])?
                    .ns_nodes(NsKind::Type)
                    .exactly_one()
                    .unwrap();
                std_resolver.resolve_in_scope(reso, path, (std_prelude.1, 0), first, paths)?;
                if reso.is_empty() {
                    self.error(path, first.span, format!(
                        "could not find `{}` in current scope", first.value));
                    return Err(());
                }
            }
        }
        assert!(!reso.is_empty());

        let anchor = anchor.map(|v| v.value);
        let more = path_items.len() > if anchor.is_some() { 0 } else { 1 };
        if more {
            let (pkg, scope) = reso.type_or_value().unwrap();
            self.with_package(pkg)
                .resolve_path_items(reso, path, (scope, 0), anchor, path_items, paths)?
        }

        assert!(!reso.is_empty());
        assert!(reso.kind() == initial_kind ||
            reso.kind() == ResolutionKind::Type && initial_kind == ResolutionKind::Exact);

        Ok(())
    }

    fn resolve_path_items(mut self,
        reso: &mut Resolution,
        node: NodeId, // For error reporting
        mut scope: ScopeVid,
        anchor: Option<&PathAnchor>,
        items: Vec<PathItem2>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<()> {
        let mut err = false;
        let start = if anchor.is_none() {
            1
        } else {
            0
        };
        for (i, item) in items.iter().enumerate().skip(start) {
            let scope_kind = self.hir.node_kind(scope.0).value;
            let type_reso = matches!(scope_kind, NodeKind::Struct | NodeKind::TypeAlias | NodeKind::TypeParam);

            // The scope must be a module if at least one is true:
            // 1. We are resolving wildcard or empty path.
            // 2. We didn't detect a type resolution condition.
            if (matches!(reso.kind, ResolutionKind::Wildcard | ResolutionKind::Empty) || !type_reso)
                && scope_kind != NodeKind::Module
            {
                self.error(node, items[i - 1].name().span, "expected module".into());
                return Err(());
            }

            if i > 0 {
                if_chain! {
                    if !type_reso;
                    if let Some(pi) = items[i - 1].as_path_item();
                    if let Some(ty_params) = pi.ty_args.as_ref();
                    then {
                        self.error(node, ty_params.span,
                            "unexpected type arguments: modules don't have type parameters".into());
                        err = true;
                    }
                }
            }

            let name = item.name();
            let name = if let Some(v) = name.value {
                name.map(|_| v)
            } else {
                assert_eq!(i, items.len() - 1);
                assert!(matches!(reso.kind, ResolutionKind::Wildcard | ResolutionKind::Empty));
                break;
            };

            reso.clear();

            if type_reso {
                reso.insert(NsKind::Type, (self.package_id, scope.0));
                reso.kind = ResolutionKind::Type;
                reso.type_path = items
                    .into_iter()
                    .skip(i - 1)
                    .map(|v| v.into_path_item().unwrap())
                    .collect();
                break;
            } else if name.value.is_self_lower() {
                assert_eq!(i, items.len() - 1);
                reso.insert(NsKind::Type, (self.package_id, scope.0));
                break;
            }
            self.resolve_in_scope(
                reso,
                node,
                scope,
                name,
                paths,
            )?;

            if let Some((pkg, sc)) = reso.type_or_value() {
                self = self.with_package(pkg);
                scope = (sc, 0);
            } else {
                let place = if i == 0 {
                    match anchor.unwrap() {
                        PathAnchor::Package { name } => if let Some(name) = name {
                            format!("package `{}`", name.value)
                        } else {
                            "package root".into()
                        }
                        PathAnchor::Super { .. } => "parent module".into(),
                    }
                } else {
                    format!("`{}`", items[i - 1].name().value.unwrap())
                };
                self.error(node, name.span, format!(
                    "could not find `{}` in {}", name.value, place));
                return Err(());
            }
        }
        if err {
            return Err(());
        }
        assert!(!reso.is_empty());
        Ok(())
    }

    fn resolve_in_scope_tree(&self,
        reso: &mut Resolution,
        node: NodeId, // for error reporting
        mut scope: ScopeVid,
        name: S<&Ident>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<()> {
        assert!(reso.is_empty());
        loop {
            self.resolve_in_scope(reso, node, scope, name, paths)?;
            if !reso.is_empty() {
                break;
            }
            if self.hir.node_kind(scope.0).value == NodeKind::Module {
                break;
            }
            scope = if let Some(v) = self.discover_data.try_parent_scope_of(scope.0) {
                v
            } else {
                break;
            };
        }
        Ok(())
    }

    fn resolve_in_scope(&self,
        reso: &mut Resolution,
        node: NodeId, // for error reporting
        scope_vid: ScopeVid,
        name: S<&Ident>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<()> {
        if let Some(scope) = self.discover_data.try_scope(scope_vid.0) {
            for ns in NsKind::iter() {
                if let Some(items) = scope.namespace(ns).get(name.value) {
                    let is_failed = items.is_failed();
                    for (id, node) in items.get(scope_vid.1) {
                        if self.hir.node_kind(node).value == NodeKind::PathEndIdent {
                            let target = self.resolve(node, paths)?;
                            for target_node in target.ns_nodes(ns) {
                                if !is_failed.is_failed(id, target_node) {
                                    reso.insert(ns, target_node);
                                }
                            }
                        } else {
                            let node = (self.package_id, node);
                            if !is_failed.is_failed(id, node) {
                                reso.insert(ns, node);
                            }
                        }
                    }
                }
            }

            // If not all namespaces were filled, look in wildcard imports.
            if !reso.is_full() {
                let mut found_in_wc_imports = Vec::new();
                for &path in scope.wildcard_imports() {
                    if_chain! {
                        if let Ok(reso) = self.resolve(path, paths);
                        if let Some((pkg, scope)) = reso.type_or_value();
                        then {
                            let mut wild_reso = Resolution::new(ResolutionKind::Exact);
                            if self.with_package(pkg)
                                .resolve_in_scope(&mut wild_reso, node, (scope, 0), name, paths).is_ok()
                            {
                                if !wild_reso.is_empty() {
                                    found_in_wc_imports.push(wild_reso);
                                }
                            }
                        }
                    }
                }
                match found_in_wc_imports.len() {
                    0 => {}
                    1 => {
                        for ns in NsKind::iter() {
                            if reso.ns_nodes_slice(ns).is_empty() {
                                for n in found_in_wc_imports[0].ns_nodes(ns) {
                                    reso.insert(ns, n);
                                }
                            }
                        }
                    }
                    _ => {
                        self.error(node, name.span, format!(
                            "`{}` found in multiple wildcard imports", name.value));
                    },
                }
            }
        }
        Ok(())
    }

    fn error(&self, node: NodeId, span: Span, text: String) {
        let source_id = self.discover_data.source_of(node, self.hir);
        if self.resolve_data.inner.borrow_mut().errors.insert((source_id, span)) {
            self.diag.borrow_mut().error_span(self.hir, self.discover_data, node, span, text);
        }
    }
}