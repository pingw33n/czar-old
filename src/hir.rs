mod display;
pub mod traverse;

use enum_as_inner::EnumAsInner;
use slab::Slab;
use std::collections::HashMap;
use std::fmt;
use std::path::PathBuf;
use std::sync::Arc;

pub use crate::syntax::{FloatLiteral, FloatTypeSuffix, IntLiteral, IntTypeSuffix, S, Span, Spanned};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct NodeId(usize);

impl NodeId {
    pub fn null() -> Self {
        Self(usize::max_value())
    }
}

impl Default for NodeId {
    fn default() -> Self {
        Self::null()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NodeKind {
    Block,
    BlockFlowCtl,
    Cast,
    FieldAccess,
    FnCall,
    FnDef,
    FnDefParam,
    IfExpr,
    Impl,
    Let,
    LetDef,
    Literal,
    Loop,
    Module,
    Op,
    Path,
    PathEndEmpty,
    PathEndIdent,
    PathEndStar,
    PathSegment,
    Range,
    Struct,
    StructType,
    StructValue,
    StructValueField,
    TypeAlias,
    TyExpr,
    TypeParam,
    Use,
    While,
}

impl NodeKind {
    pub fn is_path(self) -> bool {
        use NodeKind::*;
        match self {
            | Path
            | PathEndEmpty
            | PathEndIdent
            | PathEndStar
            | PathSegment
            => true,

            _ => false,
        }
    }
}

pub type NodeMap<T> = HashMap<NodeId, T>;

pub type SourceId = usize;

#[derive(Debug)]
pub struct Source {
    pub mod_name: Option<Ident>,
    pub path: PathBuf,
    pub text: Arc<String>,
}

#[derive(Default)]
pub struct Sources {
    sources: Slab<Source>,
}

impl Sources {
    pub fn iter(&self) -> impl Iterator<Item=(SourceId, &Source)> {
        self.sources.iter()
    }

    pub fn len(&self) -> usize {
        self.sources.len()
    }

    pub fn insert(&mut self, source: Source) -> SourceId {
        self.sources.insert(source)
    }
}

impl std::ops::Index<SourceId> for Sources {
    type Output = Source;

    fn index(&self, index: SourceId) -> &Self::Output {
        &self.sources[index]
    }
}

pub fn source_file_name(mod_name: &str) -> PathBuf {
    format!("{}.cz", mod_name).into()
}

#[derive(Default)]
pub struct Hir {
    nodes: Slab<S<NodeKind>>,
    blocks: NodeMap<Block>,
    block_flow_ctls: NodeMap<BlockFlowCtl>,
    casts: NodeMap<Cast>,
    field_accesses: NodeMap<FieldAccess>,
    fn_defs: NodeMap<FnDef>,
    fn_def_params: NodeMap<FnDefParam>,
    fn_calls: NodeMap<FnCall>,
    if_exprs: NodeMap<IfExpr>,
    impls: NodeMap<Impl>,
    lets: NodeMap<Let>,
    let_defs: NodeMap<LetDef>,
    literals: NodeMap<Literal>,
    loops: NodeMap<Loop>,
    modules: NodeMap<Module>,
    ops: NodeMap<Op>,
    paths: NodeMap<Path>,
    path_end_idents: NodeMap<PathEndIdent>,
    path_segments: NodeMap<PathSegment>,
    ranges: NodeMap<Range>,
    structs: NodeMap<Struct>,
    struct_types: NodeMap<StructType>,
    struct_values: NodeMap<StructValue>,
    struct_value_fields: NodeMap<StructValueField>,
    type_aliases: NodeMap<TypeAlias>,
    ty_exprs: NodeMap<TyExpr>,
    type_params: NodeMap<TypeParam>,
    uses: NodeMap<Use>,
    whiles: NodeMap<While>,

    sources: Sources,

    pub root: NodeId,
}

macro_rules! node_ops {
    ($($insert:ident, $get:ident, $get_mut:ident, $try_get:ident, $try_get_mut:ident, $f:ident, $ty:ident;)*) => {
        $(
        pub fn $get(&self, id: NodeId) -> &$ty {
            &self.$f[&id]
        }

        pub fn $get_mut(&mut self, id: NodeId) -> &mut $ty {
            self.$try_get_mut(id).unwrap()
        }

        pub fn $try_get(&self, id: NodeId) -> Option<&$ty> {
            self.$f.get(&id)
        }

        pub fn $try_get_mut(&mut self, id: NodeId) -> Option<&mut $ty> {
            self.$f.get_mut(&id)
        }

        pub fn $insert(&mut self, v: S<$ty>) -> NodeId {
            let id = NodeId(self.nodes.insert(v.span.spanned(NodeKind::$ty)));
            self.$f.insert(id, v.value);
            id
        }
        )*
    };
    ($($insert:ident, $is:ident, $kind:ident;)*) => {
        $(
        pub fn $is(&self, id: NodeId) -> bool {
            self.nodes.contains(id.0)
        }

        pub fn $insert(&mut self, span: Span) -> NodeId {
            NodeId(self.nodes.insert(span.spanned(NodeKind::$kind)))
        }
        )*
    };
}

impl Hir {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn sources(&self) -> &Sources {
        &self.sources
    }

    pub fn sources_mut(&mut self) -> &mut Sources {
        &mut self.sources
    }

    pub fn into_sources(self) -> Sources {
        self.sources
    }

    pub fn root_source_id(&self) -> SourceId {
        self.module(self.root).source_id.unwrap()
    }

    pub fn node_kind(&self, id: NodeId) -> S<NodeKind> {
        self.nodes[id.0]
    }

    pub fn insert_path_from_ident(&mut self, ident: S<Ident>, ty_args: Option<S<Vec<NodeId>>>) -> NodeId {
        let span = ident.span;
        let end = self.insert_path_end_ident(ident.span.spanned(PathEndIdent {
            item: PathItem {
                ident,
                ty_args,
            },
            renamed_as: None,
        }));
        let segment = self.insert_path_segment(span.spanned(PathSegment {
            prefix: Vec::new(),
            suffix: vec![end],
        }));

        self.insert_path(span.spanned(Path {
            anchor: None,
            segment,
        }))
    }

    pub fn insert_path_from_items(&mut self,
        anchor: Option<S<PathAnchor>>,
        mut items: Vec<PathItem>,
    ) -> NodeId {
        let start = anchor.map(|v| v.span.start)
            .unwrap_or(items[0].ident.span.start);

        let suffix = items.pop().unwrap();
        let suffix_start = suffix.ident.span.start;
        let end = suffix.ty_args.as_ref()
            .map(|v| v.span.end)
            .unwrap_or(suffix.ident.span.end);
        let suffix = self.insert_path_end_ident(Span::new(suffix_start, end).spanned(
            PathEndIdent {
                item: suffix,
                renamed_as: None,
            }));

        // FIXME
        let span = Span::empty();
        let segment = self.insert_path_segment(span.spanned(PathSegment {
            prefix: items,
            suffix: vec![suffix],
        }));

        self.insert_path(Span::new(start, end).spanned(Path {
            anchor,
            segment,
        }))
    }

    /// Given a `Path` node of a flat path, returns its `PathEndIdent` node.
    /// Flat path is path of a single segment with a single suffix, terminated with `PathEndIdent`
    /// node.
    /// Panics if the `node` is not `Path` or not the path is not a flat path.
    pub fn find_flat_path_end(&self, node: NodeId) -> NodeId {
        let path = self.path(node);
        let segment = self.path_segment(path.segment);
        assert_eq!(segment.suffix.len(), 1);
        if self.node_kind(segment.suffix[0]).value == NodeKind::PathEndIdent {
            segment.suffix[0]
        } else {
            panic!("invalid flat path")
        }
    }

    node_ops! {
        insert_block, block, block_mut, try_block, try_block_mut, blocks, Block;
        insert_block_flow_ctl, block_flow_ctl, block_flow_ctl_mut, try_block_flow_ctl, try_block_flow_ctl_mut, block_flow_ctls, BlockFlowCtl;
        insert_cast, cast, cast_mut, try_cast, try_cast_mut, casts, Cast;
        insert_field_access, field_access, field_access_mut, try_field_access, try_field_access_mut, field_accesses, FieldAccess;
        insert_fn_def, fn_def, fn_def_mut, try_fn_def, try_fn_def_mut, fn_defs, FnDef;
        insert_fn_def_param, fn_def_param, fn_def_param_mut, try_fn_def_param, try_fn_def_param_mut, fn_def_params, FnDefParam;
        insert_fn_call, fn_call, fn_call_mut, try_fn_call, try_fn_call_mut, fn_calls, FnCall;
        insert_if_expr, if_expr, if_expr_mut, try_if_expr, try_if_expr_mut, if_exprs, IfExpr;
        insert_impl, impl_, impl_mut, try_impl, try_impl_mut, impls, Impl;
        insert_let, let_, let_mut, try_let, try_let_mut, lets, Let;
        insert_let_def, let_def, let_def_mut, try_let_def, try_let_def_mut, let_defs, LetDef;
        insert_literal, literal, literal_mut, try_literal, try_literal_mut, literals, Literal;
        insert_loop, loop_, loop_mut, try_loop, try_loop_mut, loops, Loop;
        insert_module, module, module_mut, try_module, try_module_mut, modules, Module;
        insert_op, op, op_mut, try_op, try_op_mut, ops, Op;
        insert_path, path, path_mut, try_path, try_path_mut, paths, Path;
        insert_path_segment, path_segment, path_segment_mut, try_path_segment, try_path_segment_mut, path_segments, PathSegment;
        insert_path_end_ident, path_end_ident, path_end_ident_mut, try_path_end_ident, try_path_end_ident_mut, path_end_idents, PathEndIdent;
        insert_range, range, range_mut, try_range, try_range_mut, ranges, Range;
        insert_struct, struct_, struct_mut, try_struct, try_struct_mut, structs, Struct;
        insert_struct_type, struct_type, struct_type_mut, try_struct_type, try_struct_type_mut, struct_types, StructType;
        insert_struct_value, struct_value, struct_value_mut, try_struct_value, try_struct_value_mut, struct_values, StructValue;
        insert_struct_value_field, struct_value_field, struct_value_field_mut, try_struct_value_field, try_struct_value_field_mut, struct_value_fields, StructValueField;
        insert_type_alias, type_alias, type_alias_mut, try_type_alias, try_type_alias_mut, type_aliases, TypeAlias;
        insert_ty_expr, ty_expr, ty_expr_mut, try_ty_expr, try_ty_expr_mut, ty_exprs, TyExpr;
        insert_type_param, type_param, type_param_mut, try_type_param, try_type_param_mut, type_params, TypeParam;
        insert_use, use_, use_mut, try_use, try_use_mut, uses, Use;
        insert_while, while_, while_mut, try_while, try_while_mut, whiles, While;
    }
    node_ops! {
        insert_path_end_star, is_path_end_star, PathEndStar;
        insert_path_end_empty, is_path_end_empty, PathEndEmpty;
    }
}

#[derive(Debug, EnumAsInner)]
pub enum Op {
    Binary(BinaryOp),
    Unary(UnaryOp),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BinaryOpKind {
    Add,
    AddAssign,
    And,
    Assign,
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Div,
    DivAssign,
    Eq,
    Gt,
    GtEq,
    Index,
    Lt,
    LtEq,
    Rem,
    RemAssign,
    Mul,
    MulAssign,
    NotEq,
    Or,
    RangeExcl,
    RangeIncl,
    Shl,
    ShlAssign,
    Shr,
    ShrAssign,
    Sub,
    SubAssign,
}

impl std::fmt::Display for BinaryOpKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use BinaryOpKind::*;
        let s = match *self {
            Add => "+",
            AddAssign => "+=",
            And => "&&",
            Assign => "=",
            BitAnd => "&",
            BitAndAssign => "&=",
            BitOr => "|",
            BitOrAssign => "|=",
            BitXor => "^",
            BitXorAssign => "^=",
            Div => "/",
            DivAssign => "/=",
            Eq => "==",
            Gt => ">",
            GtEq => ">=",
            Index => "[]",
            Lt => "<",
            LtEq => "<=",
            Rem => "%",
            RemAssign => "%=",
            Mul => "*",
            MulAssign => "*=",
            NotEq => "!=",
            Or => "|",
            RangeExcl => "..",
            RangeIncl => "..=",
            Shl => "<<",
            ShlAssign => "<<=",
            Shr => ">>",
            ShrAssign => ">>=",
            Sub => "-",
            SubAssign => "-=",
        };
        f.write_str(s)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct BinaryOp {
    pub kind: S<BinaryOpKind>,
    pub left: NodeId,
    pub right: NodeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnaryOpKind {
    Addr,
    AddrMut,
    Deref,
    Neg,
    Not,
    PanickingUnwrap,
    PropagatingUnwrap,
}

impl std::fmt::Display for UnaryOpKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use UnaryOpKind::*;
        let s = match *self {
            Addr => "&",
            AddrMut => "&mut",
            Deref => "*",
            Neg => "-",
            Not => "!",
            PanickingUnwrap => "!",
            PropagatingUnwrap => "?",
        };
        f.write_str(s)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct UnaryOp {
    pub kind: S<UnaryOpKind>,
    pub arg: NodeId,
}

#[derive(Debug)]
pub struct Let {
    pub def: NodeId,
}

#[derive(Debug)]
pub struct LetDef {
    pub mut_: Option<S<()>>,
    pub name: S<Ident>,
    pub ty: Option<NodeId>,
    pub init: Option<NodeId>,
}

#[derive(Debug)]
pub struct Block {
    /// Always at least one item.
    pub exprs: Vec<NodeId>,
}

impl Block {
    pub fn empty() -> Self {
        Self {
            exprs: Vec::new(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BlockFlowCtlKind {
    Break,
    Continue,
    Return,
}

#[derive(Debug)]
pub struct BlockFlowCtl {
    pub kind: BlockFlowCtlKind,
    pub label: Option<S<Label>>,
    pub value: Option<NodeId>,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Ident(String);

impl Ident {
    const SELF_LOWER: &'static str = "self";
    const SELF_UPPER: &'static str = "Self";
    const UNDERSCORE: &'static str = "_";

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn self_lower() -> Self {
        Self(Ident::SELF_LOWER.into())
    }

    pub fn self_upper() -> Self {
        Self(Ident::SELF_UPPER.into())
    }

    pub fn underscore() -> Self {
        Self(Ident::UNDERSCORE.into())
    }

    pub fn is_self_lower(&self) -> bool {
        &self.0 == Ident::SELF_LOWER
    }

    pub fn is_self_upper(&self) -> bool {
        &self.0 == Ident::SELF_UPPER
    }

    pub fn is_underscore(&self) -> bool {
        &self.0 == Ident::UNDERSCORE
    }
}

impl std::ops::Deref for Ident {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::borrow::Borrow<str> for Ident {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<String> for Ident {
    fn from(v: String) -> Self {
        Self(v)
    }
}

impl From<&str> for Ident {
    fn from(v: &str) -> Self {
        Self::from(v.to_owned())
    }
}

impl AsRef<str> for Ident {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl PartialEq<str> for Ident {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

pub type Label = String;

/// ```
/// [pub] mod mymod;
/// [pub] mod mymod { ... }
/// ```
#[derive(Debug)]
pub struct Module {
    pub source_id: Option<SourceId>,
    pub name: Option<ModuleName>,
    pub items: Vec<NodeId>,
}

#[derive(Debug)]
pub struct ModuleName {
    pub name: S<Ident>,
    pub vis: Option<S<Vis>>,
}

#[derive(Debug)]
pub struct TypeParam {
    pub name: S<Ident>,
}

#[derive(Debug)]
pub struct FnDef {
    pub name: S<Ident>,
    pub vis: Option<S<Vis>>,
    pub ty_params: Vec<NodeId>,
    pub params: Vec<NodeId>,
    pub ret_ty: Option<NodeId>,
    pub unsafe_: Option<S<()>>,
    pub variadic: Option<S<()>>,
    pub body: Option<NodeId>,
}

impl FnDef {
    pub fn is_method(&self, hir: &Hir) -> bool {
        self.params.first()
            .map(|&p| hir.fn_def_param(p).name.value.is_self_lower())
            .unwrap_or(false)
    }
}

#[derive(Debug)]
pub struct FnDefParam {
    pub label: S<Option<Ident>>,
    pub name: S<Ident>,
    pub ty: NodeId,
}

impl FnDefParam {
    pub fn name(&self) -> S<&Ident> {
        if let Some(n) = self.label.value.as_ref() {
            self.label.span.spanned(n)
        } else {
            self.name.span.spanned(&self.name.value)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FnCallKind {
    Free,
    Method,
}

#[derive(Debug)]
pub struct FnCall {
    /// If `kind` is `Free` this is expr of function type.
    /// If `kind` is `Method` this is single-item `Path`.
    pub callee: NodeId,
    pub kind: FnCallKind,
    pub params: Vec<FnCallParam>,
}

#[derive(Debug)]
pub struct FnCallParam {
    pub name: Option<S<Ident>>,
    pub value: NodeId,
}

// struct Struct<X: Display>
// impl path::to::Struct<UInt32>
// fn foo<T, U, V>()

#[derive(Debug, EnumAsInner)]
pub enum Literal {
    Bool(bool),
    Char(char),
    String(String),
    Int(IntLiteral),
    Float(FloatLiteral),
    Unit,
}

#[derive(Debug)]
pub struct TypeAlias {
    pub vis: Option<S<Vis>>,
    pub name: S<Ident>,
    pub ty_params: Vec<NodeId>,
    pub ty: NodeId,
}

#[derive(Debug)]
pub struct TyExpr {
    pub muta: Option<S<()>>,
    pub data: S<TyData>,
}

// [<ty>]
// [<ty>*]
#[derive(Debug)]
pub struct Slice {
    pub ty: NodeId,
    pub resizable: bool,
}

#[derive(Debug, EnumAsInner)]
pub enum TyData {
    Array(Array),
    // *<ty>
    Ptr(NodeId),
    // &<ty>
    Ref(NodeId),
    Slice(Slice),
    // path::to::Type
    Path(NodeId),
    Struct(NodeId),
}

// [<ty>; <len>]
#[derive(Debug)]
pub struct Array {
    pub ty: NodeId,
    pub len: NodeId,
}

#[derive(Debug)]
pub struct Path {
    pub anchor: Option<S<PathAnchor>>,
    pub segment: NodeId, // PathSegment
}

/// `use foo::bar`;
/// `use super::foo::{bar::baz::*, doh::{*}, self}`;
/// `path::to::Trait<X, Y<Z>>`
/// `Enum::Variant`
/// `super::super::path::to::func(42)`
#[derive(Debug)]
pub struct PathSegment {
    /// ```
    /// path::to::{self, io, another::path:to:*}
    /// ^^^^  ^^             ^^^^^^^^^^^^^^^^
    /// ```
    pub prefix: Vec<PathItem>,

    /// Either `PathSegment`, `PathEndIdent`, `PathEndEmpty`, or `NodeKind::PathEndStar`
    /// ```
    /// path::to::{self, io, another::path:to::*}
    ///            ^^^^  ^^  ^                 ^
    /// ```
    pub suffix: Vec<NodeId>,
}

#[derive(Debug)]
pub struct PathItem {
    pub ident: S<Ident>,
    pub ty_args: Option<S<Vec<NodeId /*TyExpr*/>>>,
}

#[derive(Debug)]
pub struct PathEndIdent {
    pub item: PathItem,
    pub renamed_as: Option<S<Ident>>,
}

#[derive(Clone, Copy, Debug)]
pub enum PathAnchor {
    Package,
    Root,
    Super {
        count: u32,
    },
}

#[derive(Debug, EnumAsInner)]
pub enum Field {
    Ident(Ident),
    Index(u32),
}

impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Ident(v) => f.write_str(v),
            Self::Index(v) => write!(f, "{}", v),
        }
    }
}

#[derive(Debug)]
pub struct FieldAccess {
    pub receiver: NodeId,
    pub field: S<Field>,
}

#[derive(Debug)]
pub struct Cast {
    pub expr: NodeId,
    pub ty: NodeId,
}

#[derive(Debug)]
pub struct Vis {
    pub restrict: Option<S<VisRestrict>>,
}

#[derive(Debug)]
pub enum VisRestrict {
    InPackage,
}

#[derive(Debug)]
pub struct StructType {
    pub fields: Vec<StructTypeField>,
}

#[derive(Debug)]
pub struct StructTypeField {
    pub vis: Option<S<Vis>>,
    pub name: Option<S<Ident>>,
    pub ty: NodeId,
}

#[derive(Debug)]
pub struct StructValue {
    pub name: Option<NodeId>, // Path
    /// Whether the value has `0:` specifier.
    pub explicit_tuple: Option<S<()>>,
    pub fields: Vec<NodeId>, // StructValueField
}

#[derive(Debug)]
pub struct StructValueField {
    pub name: Option<S<Ident>>,
    pub value: NodeId,
}

#[derive(Debug)]
pub struct Struct {
    pub vis: Option<S<Vis>>,
    pub name: S<Ident>,
    pub ty_params: Vec<NodeId>,
    pub ty: NodeId, // StructType
}

#[derive(Debug)]
pub struct Use {
    pub vis: Option<S<Vis>>,
    pub path: NodeId,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RangeKind {
    Exclusive,
    Inclusive,
}

#[derive(Debug)]
pub struct Range {
    pub kind: RangeKind,
    pub start: Option<NodeId>,
    pub end: Option<NodeId>,
}

#[derive(Debug)]
pub struct Impl {
    pub ty_params: Vec<NodeId>,
    pub trait_: Option<NodeId>, // Path
    pub for_: NodeId, // Path
    pub items: Vec<NodeId>,
}

#[derive(Debug)]
pub struct IfExpr {
    pub cond: NodeId,
    pub if_true: NodeId,
    pub if_false: Option<NodeId>,
}

#[derive(Debug)]
pub struct While {
    pub cond: NodeId,
    pub block: NodeId,
}

#[derive(Debug)]
pub struct Loop {
    pub block: NodeId,
}