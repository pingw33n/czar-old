mod display;
mod lex;
mod parser;

use enum_as_inner::EnumAsInner;
use slab::Slab;
use std::collections::HashMap;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use lex::{Keyword, Lexer, Token};

pub use lex::{FloatLiteral, FloatTypeSuffix, IntLiteral, IntTypeSuffix, S, Span, Spanned};
pub use parser::{Fs, parse_file, parse_file_with, parse_str};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct NodeId(usize);

impl NodeId {
    pub fn null() -> Self {
        Self(usize::max_value())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NodeKind {
    Block,
    BlockFlowCtl,
    Cast,
    Empty,
    FieldAccess,
    FnDecl,
    FnCall,
    Impl,
    Literal,
    ModuleDecl,
    Op,
    Range,
    StructDecl,
    StructType,
    StructValue,
    SymPath,
    TyExpr,
    UseStmt,
    UsePath,
    VarDecl,
}

impl NodeKind {
    pub fn needs_semi(self) -> bool {
        match self {
            | Self::Block
            | Self::Impl
            | Self::FnDecl
            | Self::ModuleDecl
            | Self::StructDecl
            | Self::StructType
            => false,

            | Self::BlockFlowCtl
            | Self::Cast
            | Self::Empty
            | Self::FieldAccess
            | Self::FnCall
            | Self::Literal
            | Self::Op
            | Self::Range
            | Self::SymPath
            | Self::TyExpr
            | Self::UseStmt
            | Self::UsePath
            | Self::VarDecl
            | Self::StructValue
            => true,
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
    fn_decls: NodeMap<FnDecl>,
    fn_calls: NodeMap<FnCall>,
    impls: NodeMap<Impl>,
    literals: NodeMap<Literal>,
    module_decls: NodeMap<ModuleDecl>,
    ops: NodeMap<Op>,
    ranges: NodeMap<Range>,
    sym_paths: NodeMap<SymPath>,
    var_decls: NodeMap<VarDecl>,
    struct_decls: NodeMap<StructDecl>,
    struct_types: NodeMap<StructType>,
    struct_values: NodeMap<StructValue>,
    ty_exprs: NodeMap<TyExpr>,
    use_stmts: NodeMap<UseStmt>,
    use_paths: NodeMap<UsePath>,

    sources: Slab<Source>,

    pub root: NodeId,
}

macro_rules! ast_node_ops {
    ($($insert:ident, $get:ident, $try_get:ident, $f:ident, $ty:ident;)*) => {
        $(
        pub fn $get(&self, id: NodeId) -> &$ty {
            &self.$f[&id]
        }


        pub fn $try_get(&self, id: NodeId) -> Option<&$ty> {
            self.$f.get(&id)
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
            fn_decls: Default::default(),
            fn_calls: Default::default(),
            impls: Default::default(),
            literals: Default::default(),
            module_decls: Default::default(),
            ops: Default::default(),
            ranges: Default::default(),
            var_decls: Default::default(),
            struct_decls: Default::default(),
            struct_types: Default::default(),
            struct_values: Default::default(),
            sym_paths: Default::default(),
            ty_exprs: Default::default(),
            use_stmts: Default::default(),
            use_paths: Default::default(),
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

    pub fn insert_empty_node(&mut self, span: Span) -> NodeId {
        NodeId(self.nodes.insert(span.spanned(NodeKind::Empty)))
    }

    pub fn is_empty_node(&self, id: NodeId) -> bool {
        self.nodes[id.0].value == NodeKind::Empty
    }

    ast_node_ops! {
        insert_block, block, try_block, blocks, Block;
        insert_block_flow_ctl, block_flow_ctl, try_block_flow_ctl, block_flow_ctls, BlockFlowCtl;
        insert_cast, cast, try_cast, casts, Cast;
        insert_field_access, field_access, try_field_access, field_accesses, FieldAccess;
        insert_fn_decl, fn_decl, try_fn_decl, fn_decls, FnDecl;
        insert_fn_call, fn_call, try_fn_call, fn_calls, FnCall;
        insert_impl, impl_, try_impl, impls, Impl;
        insert_literal, literal, try_literal, literals, Literal;
        insert_module_decl, module_decl, try_module_decl, module_decls, ModuleDecl;
        insert_op, op, try_op, ops, Op;
        insert_range, range, try_range, ranges, Range;
        insert_struct_decl, struct_decl, try_struct_decl, struct_decls, StructDecl;
        insert_struct_type, struct_type, try_struct_type, struct_types, StructType;
        insert_struct_value, struct_value, try_struct_value, struct_values, StructValue;
        insert_sym_path, sym_path, try_sym_path, sym_paths, SymPath;
        insert_ty_expr, ty_expr, try_ty_expr, ty_exprs, TyExpr;
        insert_use_stmt, use_stmt, try_use_stmt, use_stmts, UseStmt;
        insert_use_path, use_path, try_use_path, use_paths, UsePath;
        insert_var_decl, var_decl, try_var_decl, var_decls, VarDecl;
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
pub struct VarDecl {
    pub muta: Option<S<()>>,
    pub name: S<Ident>,
    pub ty: Option<NodeId>,
    pub init: Option<NodeId>,
}

#[derive(Debug)]
pub struct Block {
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

pub type Ident = String;
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
pub struct FnDecl {
    pub name: S<Ident>,
    pub vis: Option<S<Vis>>,
    pub ty_args: Vec<S<Ident>>,
    pub args: Vec<FnDeclArg>,
    pub ret_ty: Option<NodeId>,
    pub unsaf: Option<S<()>>,
    pub variadic: Option<S<()>>,
    pub body: Option<NodeId>,
}

#[derive(Debug, EnumAsInner)]
pub enum FnArgName {
    Ident(Ident),
    Self_,
}

#[derive(Debug)]
pub struct FnDeclArg {
    pub pub_name: S<Option<Ident>>,
    pub priv_name: S<FnArgName>,
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
    Self_(PathTermSelf),
    Star,
}

#[derive(Debug)]
pub struct PathTermIdent {
    pub ident: S<Ident>,
    pub renamed_as: Option<S<Ident>>,
}

#[derive(Debug)]
pub struct PathTermSelf {
    pub renamed_as: Option<S<Ident>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
    /// path::to::{self, io, another::path:to::{...}}
    /// ^^^^  ^^
    /// ```
    pub prefix: Vec<S<Ident>>,

    /// ```
    /// path::to::{self, io, another::path:to::{...}}
    ///            ^^^^  ^^  ^^^^^^^^^^^^^^^^^^^^^^^
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
                ident: ident.map(PathIdent::Ident),
                ty_args: Vec::new(),
            }],
        }
    }

    // pub fn is_single(&self) -> bool {
    //     self.prefix.len() == 0 && self.terms.len() == 1
    // }

    // pub fn has_ty_args(&self) -> bool {
    //     self.prefix.iter().any(|i| !i.value.ty_args.is_empty()) ||
    //         self.terms.iter().any(|t|
    //             t.value.as_item().map(|i| !i.value.ty_args.is_empty()).unwrap_or(false))
    // }
}

#[derive(Debug)]
pub enum PathIdent {
    Ident(Ident),
    SelfType,
    SelfValue,
}

#[derive(Debug)]
pub struct PathItem {
    pub ident: S<PathIdent>,
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
    pub ty_args: Vec<S<Ident>>,
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
    pub ty_args: Vec<S<Ident>>,
    pub trait_: Option<NodeId>, // SymPath
    pub for_: NodeId, // SymPath
    pub items: Vec<NodeId>,
}

pub fn source_file_name(mod_name: &str) -> PathBuf {
    format!("{}.cz", mod_name).into()
}