use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NumberType {
    Float,
    Int {
        signed: bool,
    },
}

impl NumberType {
    pub fn kind(self) -> NumberKind {
        match self {
            Self::Float => NumberKind::Float,
            Self::Int { signed: _ } => NumberKind::Int,
        }
    }
}

#[derive(Clone, Copy, Debug, EnumAsInner, Eq, Hash, PartialEq)]
pub enum NumberKind {
    Float,
    Int,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PrimitiveType {
    Bool,
    F32,
    F64,
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    I128,
    U128,
    ISize,
    USize,
    Char,
}

impl PrimitiveType {
    pub fn as_number(self) -> Option<NumberType> {
        use PrimitiveType::*;
        Some(match self {
            | F32
            | F64
            => NumberType::Float,

            | I8
            | I16
            | I32
            | I64
            | I128
            | ISize
            => NumberType::Int { signed: true },

            | U8
            | U16
            | U32
            | U64
            | U128
            | USize
            => NumberType::Int { signed: false },

            | Bool
            | Char
            => return None,
        })
    }
}

#[derive(Clone, Copy, Debug, EnumAsInner, Eq, Hash, PartialEq)]
pub enum LangItem {
    Primitive(PrimitiveType),
    Ptr,
    Range(RangeItem),
    String,
}

impl LangItem {
    pub fn as_number(self) -> Option<NumberType> {
        self.as_primitive().and_then(|v| v.as_number())
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RangeItem {
    Range,
    RangeFrom,
    RangeFull,
    RangeInclusive,
    RangeTo,
    RangeToInclusive,
}

pub struct Lang {
    lang_item_to_type: HashMap<LangItem, LocalTypeId>,
    node_to_lang_item: HashMap<NodeId, LangItem>,
    unit_type: LocalTypeId,
}

impl Lang {
    pub fn type_(&self, ty: LangItem) -> TypeId {
        (PackageId::std(), self.lang_item_to_type[&ty])
    }

    pub fn as_item(&self, node: GlobalNodeId) -> Option<LangItem> {
        if node.0.is_std() {
            self.node_to_lang_item.get(&node.1).copied()
        } else {
            None
        }
    }

    pub fn as_primitive(&self, node: GlobalNodeId) -> Option<PrimitiveType> {
        self.as_item(node).and_then(|v| v.as_primitive().copied())
    }

    pub fn unit_type(&self) -> TypeId {
        (PackageId::std(), self.unit_type)
    }
}

impl PassImpl<'_> {
    pub fn make_lang(&mut self) -> Result<()> {
        assert!(self.package_id.is_std());

        let mut lang_item_to_type = HashMap::new();
        let mut node_to_lang_item = HashMap::new();

        {
            use LangItem as L;
            use PrimitiveType::*;
            use RangeItem as R;
            for &(lang_item, path) in &[
                (L::Primitive(Bool), &["bool"][..]),
                (L::Primitive(Char), &["char"][..]),
                (L::Primitive(F32), &["f32"][..]),
                (L::Primitive(F64), &["f64"][..]),
                (L::Primitive(I8), &["i8"][..]),
                (L::Primitive(U8), &["u8"][..]),
                (L::Primitive(I16), &["i16"][..]),
                (L::Primitive(U16), &["u16"][..]),
                (L::Primitive(I32), &["i32"][..]),
                (L::Primitive(U32), &["u32"][..]),
                (L::Primitive(I64), &["i64"][..]),
                (L::Primitive(U64), &["u64"][..]),
                (L::Primitive(I128), &["i128"][..]),
                (L::Primitive(U128), &["u128"][..]),
                (L::Primitive(ISize), &["isize"][..]),
                (L::Primitive(USize), &["usize"][..]),
                (L::Ptr, &["ptr", "Ptr"][..]),
                (L::Range(R::Range), &["ops", "Range"][..]),
                (L::Range(R::RangeFrom), &["ops", "RangeFrom"][..]),
                (L::Range(R::RangeFull), &["ops", "RangeFull"][..]),
                (L::Range(R::RangeInclusive), &["ops", "RangeInclusive"][..]),
                (L::Range(R::RangeTo), &["ops", "RangeTo"][..]),
                (L::Range(R::RangeToInclusive), &["ops", "RangeToInclusive"][..]),
                (L::String, &["string", "String"][..]),
            ] {
                let ty = self.check_lang_type(path)?;

                assert!(lang_item_to_type.insert(lang_item, ty).is_none());

                let (pkg, node) = self.underlying_type((PackageId::std(), ty)).data.name().unwrap();
                assert!(pkg.is_std());
                assert!(node_to_lang_item.insert(node, lang_item).is_none());
            }
        }

        let unit_type = self.check_lang_type(&["Unit"]).expect("error checking Unit type");

        assert!(self.check_data.lang.replace(Box::new(Lang {
            lang_item_to_type,
            node_to_lang_item,
            unit_type,
        })).is_none());

        Ok(())
    }

    pub fn std(&self) -> &Lang {
        self.check_data(PackageId::std()).lang()
    }

    fn check_lang_type(&mut self, path: &[&str]) -> Result<LocalTypeId> {
        let node = self.resolver()
            .resolve_in_package(path)
            .unwrap()
            .ns_nodes(NsKind::Type)
            .exactly_one()
            .ok_or(())?;
        assert!(node.0.is_std());
        let ty = self.ensure_typing(node.1)?;
        let ty = if let TypeData::Ctor(TypeCtor { ty: _, params }) = &self.type_(ty).data {
            if params.is_empty() {
                self.insert_type(node, TypeData::Instance(TypeInstance {
                    ty,
                    args: Vec::new(),
                }))
            } else {
                ty
            }
        } else {
            unreachable!();
        };
        let ty = self.normalize(ty);
        assert!(ty.0.is_std());
        Ok(ty.1)
    }

    pub fn as_lang_item(&self, ty: TypeId) -> Option<LangItem> {
        self.packages.as_lang_item_ctx(ty, self.cdctx())
    }

    pub fn as_primitive(&self, ty: TypeId) -> Option<PrimitiveType> {
        self.packages.as_primitive_ctx(ty, self.cdctx())
    }

    pub fn as_any_number(&self, ty: TypeId) -> Option<NumberKind> {
        self.packages.as_number_type_ctx(ty, self.cdctx()).map(|v| v.kind())
            .or_else(|| self.type_(self.underlying_type(ty).id).data.as_inference_var()
                .and_then(|v| v.as_number().copied()))
    }
}