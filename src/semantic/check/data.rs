use super::{*, Impl};

pub struct CheckData {
    pub(in super) package_id: PackageId,
    types: Slab<Type>,
    typings: NodeMap<TypeId>,
    pub(in super) lang: Option<Box<Lang>>,
    path_to_target: NodeMap<GlobalNodeId>,
    /// Maps `FieldAccess` and `StructValueField` nodes to the field index on the struct type.
    pub(in super) struct_field_index: NodeMap<u32>,
    lvalues: NodeMap<()>,
    /// Impls defined in this package.
    pub(in super) impls: HashMap<GlobalNodeId, Vec<Impl>>,
    pub(in super) entry_point: Option<NodeId>,
    pub(in super) normalized_types: TypeMap<TypeId>,
}

impl CheckData {
    pub fn new(package_id: PackageId) -> Self {
        Self {
            package_id,
            types: Default::default(),
            typings: Default::default(),
            lang: None,
            path_to_target: Default::default(),
            struct_field_index: Default::default(),
            lvalues: Default::default(),
            impls: Default::default(),
            entry_point: None,
            normalized_types: Default::default(),
        }
    }

    pub fn types<'a>(&'a self) -> impl Iterator<Item=&'a Type> + 'a {
        self.types.iter().map(|(_, v)| v)
    }

    pub fn type_(&self, id: LocalTypeId) -> &Type {
        &self.types[id.0]
    }

    pub(in super) fn type_mut(&mut self, id: LocalTypeId) -> &mut Type {
        &mut self.types[id.0]
    }

    pub(in super) fn insert_type(&mut self, node: GlobalNodeId, data: TypeData) -> TypeId {
        let e = self.types.vacant_entry();
        let id = LocalTypeId(e.key());
        e.insert(Type {
            id: (self.package_id, id),
            node,
            data,
        });
        (self.package_id, id)
    }

    pub fn typing(&self, node: NodeId) -> TypeId {
        self.typings[&node]
    }

    pub fn try_typing(&self, node: NodeId) -> Option<TypeId> {
        self.typings.get(&node).copied()
    }

    pub(in super) fn insert_typing(&mut self, node: NodeId, ty: TypeId) {
        assert!(self.typings.insert(node, ty).is_none());
    }

    pub fn lang(&self) -> &Lang {
        &*self.lang.as_ref().unwrap()
    }

    pub fn target_of(&self, path: NodeId) -> GlobalNodeId {
        self.path_to_target[&path]
    }

    pub fn try_target_of(&self, path: NodeId) -> Option<GlobalNodeId> {
        self.path_to_target.get(&path).copied()
    }

    pub(in super) fn insert_path_to_target(&mut self, path: NodeId, target: GlobalNodeId) {
        assert!(self.path_to_target.insert(path, target).is_none());
    }

    pub fn struct_field_index(&self, node: NodeId) -> u32 {
        self.struct_field_index[&node]
    }

    pub(in super) fn insert_struct_field_index(&mut self, field_node: NodeId, idx: u32) {
        assert!(self.struct_field_index.insert(field_node, idx).is_none());
    }

    pub(in super) fn set_lvalue(&mut self, node: NodeId) {
        assert!(self.lvalues.insert(node, ()).is_none());
    }

    pub fn is_lvalue(&self, node: NodeId) -> bool {
        self.lvalues.contains_key(&node)
    }

    pub fn entry_point(&self) -> Option<NodeId> {
        self.entry_point
    }

    pub fn try_normalized_type(&self, ty: TypeId) -> Option<TypeId> {
        self.normalized_types.get(&ty).copied()
    }
}