use super::*;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct StructTypeField {
    pub name: FieldAccessName,
    pub ty: TypeId,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct StructType {
    pub def: Option<GlobalNodeId>,
    pub fields: Vec<StructTypeField>,
}

impl StructType {
    pub fn is_tuple(&self) -> bool {
        self.fields.first().map(|f| f.name.as_index().is_some()).unwrap_or(true)
    }

    pub fn is_unit(&self) -> bool {
        self.fields.is_empty()
    }
}

#[derive(Debug)]
pub struct BaseStructType {
    pub name: Ident,
}

impl PassImpl<'_> {
    pub fn check_struct_type(&mut self, node: NodeId /*StructType*/) -> Result<TypeId> {
        let fields = &self.hir.struct_type(node).fields;
        let named = self.hir.node_kind(self.discover_data.parent_of(node)).value == NodeKind::Struct;

        let mut err = false;
        let mut seen_named_fields = HashSet::new();
        let mut field_tys = Vec::with_capacity(fields.len());
        for (i, f) in fields.iter().enumerate() {
            let name = if let Some(name) = f.name.as_ref() {
                if seen_named_fields.insert(&name.value) {
                    FieldAccessName::Ident(name.value.clone())
                } else {
                    self.error_span(node, name.span, format!(
                        "field `{}` is defined multiple times",
                        name.value));
                    continue;
                }
            } else {
                FieldAccessName::Index(i as u32)
            };
            if let Ok(ty) = self.typing(f.ty) {
                field_tys.push(StructTypeField {
                    name,
                    ty,
                });
            } else {
                err = true;
            }
        }
        if err {
            return Err(());
        }
        let unnamed_record = !named && !seen_named_fields.is_empty();
        if unnamed_record {
            field_tys.sort_by(|a, b| a.name.cmp(&b.name));
        }
        Ok(self.insert_type((self.package_id, node), TypeData::Struct(StructType {
            def: None,
            fields: field_tys,
        })))
    }

    pub fn check_struct_literal(&mut self, node: NodeId) -> Result<TypeId> {
        let StructLiteral {
            name,
            explicit_tuple,
            fields,
        } = self.hir.struct_literal(node);
        assert!(explicit_tuple.is_none() || !fields.is_empty());
        if name.is_some() {
            self.check_named_struct_literal(node)
        } else {
            self.check_unnamed_struct_literal(node)
        }
    }

    fn check_struct_literal_fields(&mut self,
        ty: TypeId,
        fields: &[NodeId /*StructLiteralField*/],
    ) -> HashSet<u32> {
        let mut seen_fields = HashSet::new();
        for (i, &field_node) in fields.iter().enumerate() {
            let field = self.hir.struct_literal_field(field_node);

            let name = if let Some(name) = &field.name {
                name.span.spanned(FieldAccessName::Ident(name.value.clone()))
            } else {
                self.hir.node_kind(field.value).span.spanned(FieldAccessName::Index(i as u32))
            };

            let expected_ty = if let Ok(v) = self.resolve_struct_field(ty, field_node, &name) {
                v
            } else {
                continue;
            };

            if !seen_fields.insert(self.check_data.struct_field_index[&field_node]) {
                self.error_span(field_node, name.span, format!(
                    "field `{}` is initialized multiple times",
                    name.value));
                continue;
            }

            let actual_ty = if let Ok(ty) = self.typing(field_node) {
                ty
            } else {
                continue;
            };

            self.unify(actual_ty, expected_ty);
            if self.normalize(expected_ty) != self.normalize(actual_ty) {
                let text = format!(
                    "mismatching types in struct `{struct_ty}` field `{field}`: expected `{exp}`, found `{act}`",
                    struct_ty = self.display_type(ty),
                    field = name.value,
                    exp = self.display_type(expected_ty),
                    act = self.display_type(actual_ty));
                self.error(field.value, text);
            }
        }
        seen_fields
    }

    fn check_named_struct_literal(&mut self, node: NodeId) -> Result<TypeId> {
        let StructLiteral {
            name,
            explicit_tuple: _,
            fields,
        } = self.hir.struct_literal(node);

        let name = name.unwrap();

        let ty = self.typing(name)?;
        let ty = self.normalize(ty);
        if self.underlying_type(ty).data.as_struct().and_then(|v| v.def).is_none() {
            self.error(name, "expected named struct".into());
            return Err(());
        }

        let seen_fields = self.check_struct_literal_fields(ty, fields);

        let sty = self.underlying_type(ty).data.as_struct().unwrap();

        let expected_field_count = sty.fields.len();
        if seen_fields.len() != expected_field_count {
            assert!(seen_fields.len() < expected_field_count);

            if sty.is_tuple() {
                self.error(node, format!(
                    "missing field{} in initializer of tuple struct `{}`: expected {} field{}",
                    if expected_field_count > 1 { "s" } else { "" },
                    self.display_type(ty),
                    expected_field_count, if expected_field_count > 1 { "s" } else { "" }));
            } else {
                let mut missing_fields = Vec::new();
                for (i, f) in sty.fields.iter().enumerate() {
                    if seen_fields.contains(&(i as u32)) {
                        continue;
                    }
                    missing_fields.push(f.name.as_ident().unwrap());
                }
                assert!(!missing_fields.is_empty());
                missing_fields.sort();
                self.error(node, format!(
                    "missing field{} {} in initializer of struct `{}`",
                    if missing_fields.len() > 1 { "s" } else { "" },
                    missing_fields.into_iter().map(|s| format!("`{}`", s)).collect::<Vec<_>>().join(", "),
                    self.display_type(ty)));
            }
        }

        Ok(ty)
    }

    fn check_unnamed_struct_literal(&mut self, node: NodeId /*StructLiteral*/) -> Result<TypeId> {
        let fields = &self.hir.struct_literal(node).fields;
        let mut err = false;

        let mut field_data = Vec::with_capacity(fields.len());
        let mut seen_named_fields = HashSet::new();
        for (idx, &field_node) in fields.iter().enumerate() {
            let f = self.hir.struct_literal_field(field_node);
            if let Ok(ty) = self.typing(f.value) {
                let name = if let Some(name) = f.name.as_ref() {
                    if seen_named_fields.insert(&name.value) {
                        FieldAccessName::Ident(name.value.clone())
                    } else {
                        self.error_span(node, name.span, format!(
                            "field `{}` is defined multiple times",
                            name.value));
                        err = true;
                        continue;
                    }
                } else {
                    FieldAccessName::Index(idx as u32)
                };
                field_data.push((field_node, StructTypeField {
                    name,
                    ty,
                }));
            } else {
                err = true;
            }
        }
        if err {
            return Err(());
        }
        let unnamed_record = !seen_named_fields.is_empty();
        if unnamed_record {
            field_data.sort_by(|(_, a), (_, b)| a.name.cmp(&b.name));
        }

        let mut fields = Vec::with_capacity(field_data.len());
        for (idx, (field_node, field_ty)) in field_data.into_iter().enumerate() {
            self.check_data.insert_struct_field_index(field_node, idx as u32);
            fields.push(field_ty);
        }

        Ok(self.insert_type((self.package_id, node), TypeData::Struct(StructType {
            def: None,
            fields,
        })))
    }

    pub fn resolve_struct_field(&mut self,
        struct_ty: TypeId,
        field_node: NodeId,
        field_name: &S<FieldAccessName>,
    ) -> Result<TypeId> {
        let struct_ty = self.normalize(struct_ty);
        let idx_and_ty = if_chain! {
            if let Some(sty) = self.underlying_type(struct_ty).data.as_struct();
            if self.as_primitive(struct_ty).is_none();
            then {
                // TODO Maybe optimize this.
                sty.fields.iter().enumerate()
                    .filter(|(_, f)| &f.name == &field_name.value)
                    .map(|(idx, f)| (idx as u32, f.ty))
                    .next()
            } else {
                None
            }
        };
        if let Some((idx, ty)) = idx_and_ty {
            self.check_data.insert_struct_field_index(field_node, idx);
            Ok(ty)
        } else {
            self.error_span(field_node, field_name.span, format!(
                "unknown field `{}` on type `{}`",
                field_name.value, self.display_type(struct_ty)));
            Err(())
        }
    }

    pub fn is_unit_type(&self, ty: TypeId) -> bool {
        self.packages.is_unit_type_ctx(ty, self.cdctx())
    }
}