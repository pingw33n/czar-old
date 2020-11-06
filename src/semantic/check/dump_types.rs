use std::fmt::Write;

use super::{*, StructType};

impl PassImpl<'_> {
    pub fn dump_all_types(&self) {
        for ty in self.check_data.base_types() {
            println!("{}", self.dump_base_type(ty.id()));
        }
        for ty in self.check_data.types() {
            println!("{}", self.dump_type(ty.id));
        }
    }

    #[must_use]
    pub fn dump_base_type(&self, ty: BaseTypeId) -> String {
        let ty = self.base_type(ty);
        let mut s = String::new();
        write!(s, "{:12} ", self.base_type_id_str(ty.id())).unwrap();
        match &ty.data {
            BaseTypeData::Struct(BaseStructType { name }) => {
                write!(s, "Struct(name: {})", name).unwrap();
            }
        }
        s
    }

    #[must_use]
    pub fn dump_type(&self, ty: TypeId) -> String {
        let ty = self.type_(ty);
        let mut s = String::new();
        write!(s, "{:12} {:32} ", self.type_id_str(ty.id), self.node_kind_str(ty.node)).unwrap();
        match &ty.data {
            TypeData::Fn(FnType { params, ty_params, result, unsafe_ }) => {
                write!(s, "Fn(params: {}, ty_params: {}, result: {}, unsafe: {})",
                    self.type_list_str(params),
                    self.type_list_str(ty_params),
                    self.type_id_str(*result),
                    unsafe_).unwrap();
            }
            TypeData::Incomplete(IncompleteType { params }) => {
                write!(s, "Incomplete(params: {})", self.type_list_str(params)).unwrap();
            }
            TypeData::Instance(TypeInstance { ty, data }) => {
                write!(s, "Instance(ty: {}, ", self.type_id_str(*ty)).unwrap();
                match data {
                    TypeInstanceData::Args(v) => write!(s, " args: {}", self.type_list_str(v)).unwrap(),
                    TypeInstanceData::Params(v) => write!(s, " params: {}", self.type_list_str(v)).unwrap(),
                }
                s.push_str(")");
            }
            TypeData::Struct(v) => {
                write!(s, "{}", self.struct_type_str(v)).unwrap();
            }
            &TypeData::Var(var) => {
                let var = match var {
                    Var::Inference(var) => {
                        match var {
                            InferenceVar::Any => format!("?{}", ty.id.1.0),
                            InferenceVar::Number(nk) => format!("?{:?}'{}", nk, ty.id.1.0)
                        }
                    }
                    Var::Param => {
                        let name = &self.hir(ty.node.0).type_param(ty.node.1).name.value;
                        format!("{}'{}", name, ty.id.1.0)
                    }
                };
                write!(s, "Var({})", var).unwrap();
            }
        }
        s
    }

    fn package_name(&self, id: PackageId) -> &Ident {
        if id == self.package_id {
            self.package_name
        } else {
            &self.packages[id].name
        }
    }

    fn type_id_str(&self, id: TypeId) -> String {
        format!("{}.{}", self.package_name(id.0), id.1.0)
    }

    fn base_type_id_str(&self, id: BaseTypeId) -> String {
        format!("{}.B{}", self.package_name(id.0), id.1.0)
    }

    fn node_kind_str(&self, node: GlobalNodeId) -> String {
        let nk = self.hir(node.0).node_kind(node.1);
        format!("{}.{:?} @{}..{}", self.package_name(node.0), nk.value, nk.span.start, nk.span.end)
    }

    fn type_list_str(&self, tys: &[TypeId]) -> String {
        let mut s = String::new();
        s.push('[');
        for (i, &ty) in tys.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            s.push_str(&self.type_id_str(ty));
        }
        s.push(']');
        s
    }

    fn struct_fields_str(&self, fields: &[StructTypeField]) -> String {
        let mut s = String::new();
        s.push('[');
        for (i, StructTypeField { name, ty }) in fields.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            write!(s, "{}: {}", name, self.type_id_str(*ty)).unwrap();
        }
        s.push(']');
        s
    }

    fn struct_type_str(&self, v: &StructType) -> String {
        let StructType { base, fields } = v;
        format!("Struct(base: {:?}, fields: {})",
            base.map(|bty| self.base_type_id_str(bty)),
            self.struct_fields_str(fields))
    }
}