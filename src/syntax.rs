mod display;
mod lex;
mod parse;
pub mod traverse;

use enum_as_inner::EnumAsInner;
use slab::Slab;
use std::collections::HashMap;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use lex::{Keyword, Lexer, Token};

pub use lex::{FloatLiteral, FloatTypeSuffix, IntLiteral, IntTypeSuffix, S, Span, Spanned};
pub use parse::{Fs, parse_file, parse_file_with, parse_str};

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
    Fn_,
    FnDecl,
    FnDeclArg,
    IfExpr,
    Impl,
    Let,
    LetDecl,
    Literal,
    Loop,
    ModuleDecl,
    Op,
    Range,
    StructDecl,
    StructType,
    StructValue,
    SymPath,
    TyExpr,
    TypeArg,
    UsePath,
    UseStmt,
    While,
}

impl NodeKind {
    /// Statements don't need ';' delimiter in blocks and modules.
    pub fn is_stmt(self) -> bool {
        match self {
            | Self::Block
            | Self::Impl
            | Self::IfExpr
            | Self::Loop
            | Self::Fn_
            | Self::ModuleDecl
            | Self::StructDecl
            | Self::StructType
            | Self::While
            => true,

            | Self::BlockFlowCtl
            | Self::Cast
            | Self::FieldAccess
            | Self::FnCall
            | Self::FnDecl
            | Self::FnDeclArg
            | Self::Literal
            | Self::Op
            | Self::Range
            | Self::SymPath
            | Self::TyExpr
            | Self::TypeArg
            | Self::UseStmt
            | Self::UsePath
            | Self::Let
            | Self::LetDecl
            | Self::StructValue
            => false,
        }
    }
}

pub type NodeMap<T> = HashMap<NodeId, T>;

pub type SourceId = usize;

#[derive(Debug)]
pub struct Source {
    pub mod_name: Option<Ident>,
    pub path: PathBuf,
}

#[derive(Debug)]
pub struct Ast {
    nodes: Slab<S<NodeKind>>,
    blocks: NodeMap<Block>,
    block_flow_ctls: NodeMap<BlockFlowCtl>,
    casts: NodeMap<Cast>,
    field_accesses: NodeMap<FieldAccess>,
    fns: NodeMap<Fn_>,
    fn_decls: NodeMap<FnDecl>,
    fn_decl_args: NodeMap<FnDeclArg>,
    fn_calls: NodeMap<FnCall>,
    if_exprs: NodeMap<IfExpr>,
    impls: NodeMap<Impl>,
    lets: NodeMap<Let>,
    let_decls: NodeMap<LetDecl>,
    literals: NodeMap<Literal>,
    loops: NodeMap<Loop>,
    module_decls: NodeMap<ModuleDecl>,
    ops: NodeMap<Op>,
    ranges: NodeMap<Range>,
    sym_paths: NodeMap<SymPath>,
    struct_decls: NodeMap<StructDecl>,
    struct_types: NodeMap<StructType>,
    struct_values: NodeMap<StructValue>,
    ty_exprs: NodeMap<TyExpr>,
    type_args: NodeMap<TypeArg>,
    use_stmts: NodeMap<UseStmt>,
    use_paths: NodeMap<UsePath>,
    whiles: NodeMap<While>,

    sources: Slab<Source>,

    pub root: NodeId,
}

macro_rules! ast_node_ops {
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
}

impl Ast {
    pub fn new() -> Self {
        Self {
            nodes: Default::default(),
            blocks: Default::default(),
            block_flow_ctls: Default::default(),
            casts: Default::default(),
            field_accesses: Default::default(),
            fns: Default::default(),
            fn_decls: Default::default(),
            fn_decl_args: Default::default(),
            fn_calls: Default::default(),
            if_exprs: Default::default(),
            impls: Default::default(),
            lets: Default::default(),
            let_decls: Default::default(),
            literals: Default::default(),
            loops: Default::default(),
            module_decls: Default::default(),
            ops: Default::default(),
            ranges: Default::default(),
            struct_decls: Default::default(),
            struct_types: Default::default(),
            struct_values: Default::default(),
            sym_paths: Default::default(),
            ty_exprs: Default::default(),
            type_args: Default::default(),
            use_stmts: Default::default(),
            use_paths: Default::default(),
            whiles: Default::default(),
            sources: Default::default(),
            root: NodeId::null(),
        }
    }

    pub fn source(&self, id: SourceId) -> &Source {
        &self.sources[id]
    }

    pub fn insert_source(&mut self, source: Source) -> SourceId {
        self.sources.insert(source)
    }

    pub fn node_kind(&self, id: NodeId) -> S<NodeKind> {
        self.nodes[id.0]
    }

    ast_node_ops! {
        insert_block, block, block_mut, try_block, try_block_mut, blocks, Block;
        insert_block_flow_ctl, block_flow_ctl, block_flow_ctl_mut, try_block_flow_ctl, try_block_flow_ctl_mut, block_flow_ctls, BlockFlowCtl;
        insert_cast, cast, cast_mut, try_cast, try_cast_mut, casts, Cast;
        insert_field_access, field_access, field_access_mut, try_field_access, try_field_access_mut, field_accesses, FieldAccess;
        insert_fn, fn_, fn_mut, try_fn, try_fn_mut, fns, Fn_;
        insert_fn_decl, fn_decl, fn_decl_mut, try_fn_decl, try_fn_decl_mut, fn_decls, FnDecl;
        insert_fn_decl_arg, fn_decl_arg, fn_decl_arg_mut, try_fn_decl_arg, try_fn_decl_arg_mut, fn_decl_args, FnDeclArg;
        insert_fn_call, fn_call, fn_call_mut, try_fn_call, try_fn_call_mut, fn_calls, FnCall;
        insert_if_expr, if_expr, if_expr_mut, try_if_expr, try_if_expr_mut, if_exprs, IfExpr;
        insert_impl, impl_, impl_mut, try_impl, try_impl_mut, impls, Impl;
        insert_let, let_, let_mut, try_let, try_let_mut, lets, Let;
        insert_let_decl, let_decl, let_decl_mut, try_let_decl, try_let_decl_mut, let_decls, LetDecl;
        insert_literal, literal, literal_mut, try_literal, try_literal_mut, literals, Literal;
        insert_loop, loop_, loop_mut, try_loop, try_loop_mut, loops, Loop;
        insert_module_decl, module_decl, module_decl_mut, try_module_decl, try_module_decl_mut, module_decls, ModuleDecl;
        insert_op, op, op_mut, try_op, try_op_mut, ops, Op;
        insert_range, range, range_mut, try_range, try_range_mut, ranges, Range;
        insert_struct_decl, struct_decl, struct_decl_mut, try_struct_decl, try_struct_decl_mut, struct_decls, StructDecl;
        insert_struct_type, struct_type, struct_type_mut, try_struct_type, try_struct_type_mut, struct_types, StructType;
        insert_struct_value, struct_value, struct_value_mut, try_struct_value, try_struct_value_mut, struct_values, StructValue;
        insert_sym_path, sym_path, sym_path_mut, try_sym_path, try_sym_path_mut, sym_paths, SymPath;
        insert_ty_expr, ty_expr, ty_expr_mut, try_ty_expr, try_ty_expr_mut, ty_exprs, TyExpr;
        insert_type_arg, type_arg, type_arg_mut, try_type_arg, try_type_arg_mut, type_args, TypeArg;
        insert_use_stmt, use_stmt, use_stmt_mut, try_use_stmt, try_use_stmt_mut, use_stmts, UseStmt;
        insert_use_path, use_path, use_path_mut, try_use_path, try_use_path_mut, use_paths, UsePath;
        insert_while, while_, while_mut, try_while, try_while_mut, whiles, While;
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

#[derive(Debug)]
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

#[derive(Debug)]
pub struct UnaryOp {
    pub kind: S<UnaryOpKind>,
    pub arg: NodeId,
}

#[derive(Debug)]
pub struct Let {
    pub decl: NodeId,
}

#[derive(Debug)]
pub struct LetDecl {
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

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Ident(String);

impl Ident {
    const SELF_VALUE: &'static str = "self";
    const SELF_TYPE: &'static str = "Self";

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn self_value() -> Self {
        Self(Ident::SELF_VALUE.into())
    }

    pub fn self_type() -> Self {
        Self(Ident::SELF_TYPE.into())
    }

    pub fn is_self_value(&self) -> bool {
        &self.0 == Ident::SELF_VALUE
    }

    pub fn is_self_type(&self) -> bool {
        &self.0 == Ident::SELF_TYPE
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
pub struct ModuleDecl {
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
pub struct TypeArg {
    pub name: S<Ident>,
}

#[derive(Debug)]
pub struct Fn_ {
    pub decl: NodeId,
}

#[derive(Debug)]
pub struct FnDecl {
    pub name: S<Ident>,
    pub vis: Option<S<Vis>>,
    pub ty_args: Vec<NodeId>,
    pub args: Vec<NodeId>,
    pub ret_ty: Option<NodeId>,
    pub unsafe_: Option<S<()>>,
    pub variadic: Option<S<()>>,
    pub body: Option<NodeId>,
}

#[derive(Debug)]
pub struct FnDeclArg {
    pub pub_name: S<Option<Ident>>,
    pub priv_name: S<Ident>,
    pub ty: NodeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FnCallKind {
    Free,
    Method,
}

#[derive(Debug)]
pub struct FnCall {
    pub callee: NodeId,
    pub kind: FnCallKind,
    pub args: Vec<FnCallArg>,
}

#[derive(Debug)]
pub struct FnCallArg {
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
    SymPath(NodeId),
    Struct(NodeId),
}

// [<ty>; <len>]
#[derive(Debug)]
pub struct Array {
    pub ty: NodeId,
    pub len: NodeId,
}

/// Use path terminator.
#[derive(Debug, EnumAsInner)]
pub enum PathTerm {
    Ident(PathTermIdent),
    Path(NodeId),
    Star,
}

#[derive(Debug)]
pub struct PathTermIdent {
    pub ident: S<Ident>,
    pub renamed_as: Option<S<Ident>>,
}

#[derive(Clone, Copy, Debug)]
pub enum PathAnchor {
    Package,
    Root,
    Super {
        count: u32,
    }
}

// use foo::bar;
// use super::foo::{bar::baz::*, doh::{*}, self};
#[derive(Debug)]
pub struct UsePath {
    /// ```
    /// path::to::{self, io, another::path:to:*}
    /// ^^^^  ^^             ^^^^^^^^^^^^^^^^
    /// ```
    pub prefix: Vec<S<Ident>>,

    /// ```
    /// path::to::{self, io, another::path:to::*}
    ///            ^^^^  ^^                    ^
    /// ```
    /// Never empty.
    pub terms: Vec<S<PathTerm>>,
}

/// Path to symbol.
/// `path::to::Trait<X, Y<Z>>`
/// `Enum::Variant`
/// `super::super::path::to::func(42)`
#[derive(Debug)]
pub struct SymPath {
    pub anchor: Option<S<PathAnchor>>,

    /// Never empty.
    pub items: Vec<PathItem>,
}

impl SymPath {
    pub fn from_ident(ident: S<Ident>) -> Self {
        Self {
            anchor: None,
            items: vec![PathItem {
                ident,
                ty_args: Vec::new(),
            }],
        }
    }
}

#[derive(Debug)]
pub struct PathItem {
    pub ident: S<Ident>,
    pub ty_args: Vec<NodeId>, // TyExpr
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
    pub name: Option<NodeId>, // SymPath
    /// Whether the value had `0:` specifier.
    pub anonymous_fields: Option<S<()>>,
    pub fields: Vec<StructValueField>,
}

#[derive(Debug)]
pub struct StructValueField {
    pub name: Option<S<Ident>>,
    pub value: NodeId,
}

#[derive(Debug)]
pub struct StructDecl {
    pub vis: Option<S<Vis>>,
    pub name: S<Ident>,
    pub ty_args: Vec<NodeId>,
    pub ty: NodeId,
}

#[derive(Debug)]
pub struct UseStmt {
    pub vis: Option<S<Vis>>,
    pub path: S<AnchoredPath>,
}

#[derive(Debug)]
pub struct AnchoredPath {
    pub anchor: Option<PathAnchor>,
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
    pub ty_args: Vec<NodeId>,
    pub trait_: Option<NodeId>, // SymPath
    pub for_: NodeId, // SymPath
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

pub fn source_file_name(mod_name: &str) -> PathBuf {
    format!("{}.cz", mod_name).into()
}