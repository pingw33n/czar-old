use slab::Slab;

use crate::hir::{Hir, Ident, NodeId};
use crate::semantic::discover::DiscoverData;
use crate::semantic::resolve::ResolveData;
use crate::semantic::type_check::Types;
use std::collections::HashMap;
use std::ops::Index;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PackageKind {
    Exe,
    Lib,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct PackageId(usize);

impl PackageId {
    const STD: Self = Self(0);

    pub fn null() -> Self {
        Self(usize::max_value())
    }

    pub const fn std() -> Self {
        PackageId::STD
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

pub struct Package {
    pub id: PackageId,
    pub name: Ident,
    pub hir: Hir,
    pub discover_data: DiscoverData,
    pub resolve_data: ResolveData,
    pub types: Types,
}

#[derive(Default)]
pub struct Packages {
    packages: Slab<Package>,
    by_name: HashMap<Ident, PackageId>,
}

impl Packages {
    pub fn next_id(&mut self) -> PackageId {
        PackageId(self.packages.vacant_entry().key())
    }

    pub fn insert(&mut self, id: PackageId, package: Package) {
        self.by_name.insert(package.name.clone(), id);
        let e = self.packages.vacant_entry();
        assert_eq!(e.key(), id.0);
        e.insert(package);
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item=(PackageId, &'a Package)> + 'a {
        self.packages.iter().map(|(id, v)| (PackageId(id), v))
    }

    pub fn try_by_name(&self, name: &str) -> Option<PackageId> {
        self.by_name.get(name).copied()
    }
}

impl Index<PackageId> for Packages {
    type Output = Package;

    fn index(&self, index: PackageId) -> &Self::Output {
        &self.packages[index.0]
    }
}