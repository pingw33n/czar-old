use std::fmt::Write;

use super::{*, StructType};

impl PassImpl<'_> {
    pub fn dump_all_types(&self) {
        for ty in self.check_data.types() {
            println!("{}", self.dump_type(ty.id));
        }
    }

    #[must_use]
    pub fn dump_type(&self, ty: TypeId) -> String {
        let ty = self.type_(ty);
        let mut s = String::new();
        write!(s, "{:12} {:32} ", self.type_id_str(ty.id), self.node_kind_str(ty.node)).unwrap();
        match &ty.data {
            TypeData::Ctor(TypeCtor { ty, params }) => {
                write!(s, "Ctor(ty: {}, params: {})", self.type_id_str(*ty), self.type_list_str(params)).unwrap();
            }
            TypeData::Fn(FnType { name, params, result, unsafe_ }) => {
                let name = if let &Some(name) = name {
                    let nk = self.node_kind_str(name);
                    let name = &self.hir(name.0).fn_def(name.1).name.value;
                    format!("name: `{}` {}, ", name, nk)
                } else {
                    "".into()
                };
                write!(s, "Fn({}params: {}, result: {}, unsafe: {})",
                    name,
                    self.type_list_str(params),
                    self.type_id_str(*result),
                    unsafe_).unwrap();
            }
            TypeData::GenericEnv(GenericEnv { ty, vars }) => {
                let mut vars_str = String::new();
                for (i, (var, val)) in vars.iter().enumerate() {
                    if i > 0 {
                        vars_str.push_str(", ");
                    }
                    write!(vars_str, "{}={}",
                        self.type_param_str(*self.type_(var).data.as_var().unwrap().as_param().unwrap()),
                        self.type_id_str(val)).unwrap();
                }
                write!(s, "GenericEnv(ty: {}, vars: [{}])", self.type_id_str(*ty), vars_str).unwrap();
            }
            TypeData::Incomplete(IncompleteType { params }) => {
                write!(s, "Incomplete(params: {})", self.type_list_str(params)).unwrap();
            }
            TypeData::Instance(TypeInstance { ty, args }) => {
                write!(s, "Instance(ty: {}, args: {})", self.type_id_str(*ty), self.type_list_str(args)).unwrap();
            }
            &TypeData::Slice(SliceType { item, len }) => {
                write!(s, "Slice(item: {}, len: {:?})", self.type_id_str(item), len).unwrap();
            }
            TypeData::Struct(StructType { name, fields }) => {
                write!(s, "Struct(").unwrap();
                if let &Some(name) = name {
                    let nk = self.node_kind_str(name);
                    let name = &self.hir(name.0).struct_(name.1).name.value;
                    write!(s, "name: `{}` {}, ", name, nk).unwrap();
                }
                write!(s, "fields: [").unwrap();
                for (i, StructTypeField { name, ty }) in fields.iter().enumerate() {
                    if i > 0 {
                        s.push_str(", ");
                    }
                    write!(s, "{}: {}", name, self.type_id_str(*ty)).unwrap();
                }
                write!(s, "]").unwrap();
            }
            &TypeData::Var(var) => {
                let var = match var {
                    Var::Inference(var) => {
                        match var {
                            InferenceVar::Any { inhabited } => format!("?{}{}",
                                if inhabited { "" } else { "Never'" },
                                ty.id.1.0),
                            InferenceVar::Number(nk) => format!("?{:?}'{}", nk, ty.id.1.0)
                        }
                    }
                    Var::Param(node) => self.type_param_str(node)
                };
                write!(s, "Var({})", var).unwrap();
            }
        }
        s
    }

    fn type_param_str(&self, node: GlobalNodeId) -> String {
        let name = &self.hir(node.0).type_param(node.1).name.value;
        format!("{}'{}_{}", name, node.0.as_u32(), node.1.as_u32())
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
}