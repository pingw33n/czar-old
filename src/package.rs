use std::collections::HashMap;
use std::ops::Index;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::hir::{Hir, Ident, NodeId};
use crate::semantic::discover::DiscoverData;
use crate::semantic::resolve::ResolveData;
use crate::semantic::type_check::Types;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageKind {
    Exe,
    Lib,
}

static NEXT_ID: AtomicU32 = AtomicU32::new(PackageId::std().0 + 1);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct PackageId(u32);

impl PackageId {
    pub fn new() -> Self {
        let id = NEXT_ID.fetch_add(1, Ordering::SeqCst);
        assert!(id < u32::max_value());
        Self(id)
    }

    pub fn null() -> Self {
        Self(u32::max_value())
    }

    pub const fn std() -> Self {
        Self(0)
    }

    pub const fn is_std(self) -> bool {
        self.0 == Self::std().0
    }
}

impl Default for PackageId {
    fn default() -> Self {
        Self::null()
    }
}

pub type GlobalNodeId = (PackageId, NodeId);

pub type PackageRef = Arc<Package>;

pub struct Package {
    pub id: PackageId,
    pub name: Ident,
    pub hir: Hir,
    pub discover_data: DiscoverData,
    pub resolve_data: ResolveData,
    pub types: Types,
}

#[derive(Clone, Default)]
pub struct Packages {
    by_id: HashMap<PackageId, PackageRef>,
    by_name: HashMap<Ident, PackageRef>,
}

impl Packages {
    pub fn insert(&mut self, package: PackageRef) {
        assert!(self.by_id.insert(package.id, package.clone()).is_none());
        assert!(self.by_name.insert(package.name.clone(), package).is_none());
    }

    pub fn try_by_name(&self, name: &str) -> Option<&Package> {
        self.by_name.get(name).map(|v| &**v)
    }
}

impl Index<PackageId> for Packages {
    type Output = Package;

    fn index(&self, index: PackageId) -> &Self::Output {
        &self.by_id[&index]
    }
}
