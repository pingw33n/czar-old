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
pub use parser::{parse_file, parse_str};
use std::fmt::Write;

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
    Cast,
    Empty,
    FieldAccess,
    FnDecl,
    FnCall,
    Literal,
    ModuleDecl,
    Op,
    StructDecl,
    SymPath,
    TyExpr,
    UseStmt,
    UsePath,
    VarDecl,
}

pub type NodeMap<T> = HashMap<NodeId, T>;

#[derive(Debug)]
pub struct Ast {
    nodes: Slab<NodeKind>,
    blocks: NodeMap<Block>,
    casts: NodeMap<Cast>,
    field_accesses: NodeMap<FieldAccess>,
    fn_decls: NodeMap<FnDecl>,
    fn_calls: NodeMap<FnCall>,
    literals: NodeMap<Literal>,
    module_decls: NodeMap<ModuleDecl>,
    ops: NodeMap<Op>,
    sym_paths: NodeMap<SymPath>,
    var_decls: NodeMap<VarDecl>,
    struct_decls: NodeMap<StructDecl>,
    ty_exprs: NodeMap<TyExpr>,
    use_stmts: NodeMap<UseStmt>,
    use_paths: NodeMap<UsePath>,

    pub root: S<NodeId>,
}

macro_rules! ast_node_ops {
    ($($insert:ident, $get:ident, $f:ident, $ty:ident;)*) => {
        $(
        pub fn $get(&self, id: NodeId) -> &$ty {
            &self.$f[&id]
        }

        pub fn $insert(&mut self, v: $ty) -> NodeId {
            let id = NodeId(self.nodes.insert(NodeKind::$ty));
            self.$f.insert(id, v);
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
            casts: Default::default(),
            field_accesses: Default::default(),
            fn_decls: Default::default(),
            fn_calls: Default::default(),
            literals: Default::default(),
            module_decls: Default::default(),
            ops: Default::default(),
            var_decls: Default::default(),
            struct_decls: Default::default(),
            sym_paths: Default::default(),
            ty_exprs: Default::default(),
            use_stmts: Default::default(),
            use_paths: Default::default(),
            root: Span::new(0, 0).spanned(NodeId::null()),
        }
    }

    pub fn node_kind(&self, id: NodeId) -> NodeKind {
        self.nodes[id.0]
    }

    pub fn insert_empty_node(&mut self) -> NodeId {
        NodeId(self.nodes.insert(NodeKind::Empty))
    }

    pub fn is_empty_node(&self, id: NodeId) -> bool {
        self.nodes[id.0] == NodeKind::Empty
    }

    ast_node_ops! {
        insert_block, block, blocks, Block;
        insert_cast, cast, casts, Cast;
        insert_field_access, field_access, field_accesses, FieldAccess;
        insert_fn_decl, fn_decl, fn_decls, FnDecl;
        insert_fn_call, fn_call, fn_calls, FnCall;
        insert_literal, literal, literals, Literal;
        insert_module_decl, module_decl, module_decls, ModuleDecl;
        insert_op, op, ops, Op;
        insert_struct_decl, struct_decl, struct_decls, StructDecl;
        insert_sym_path, sym_path, sym_paths, SymPath;
        insert_ty_expr, ty_expr, ty_exprs, TyExpr;
        insert_use_stmt, use_stmt, use_stmts, UseStmt;
        insert_use_path, use_path, use_paths, UsePath;
        insert_var_decl, var_decl, var_decls, VarDecl;
    }
}

#[derive(Debug)]
pub enum Op {
    BinaryOp(BinaryOp),
    Unary(UnaryOp),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BinaryOpKind {
    Add,
    Div,
    Mul,
    Sub,
}

impl fmt::Display for BinaryOpKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use BinaryOpKind::*;
        f.write_char(match self {
            Add => '+',
            Div => '/',
            Mul => '*',
            Sub => '-',
        })
    }
}

#[derive(Debug)]
pub struct BinaryOp {
    pub kind: S<BinaryOpKind>,
    pub left: S<NodeId>,
    pub right: S<NodeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnaryOpKind {
    Neg,
}

impl fmt::Display for UnaryOpKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use UnaryOpKind::*;
        f.write_char(match self {
            Neg => '-',
        })
    }
}

#[derive(Debug)]
pub struct UnaryOp {
    pub kind: S<UnaryOpKind>,
    pub arg: S<NodeId>,
}

#[derive(Debug)]
pub struct VarDecl {
    pub muta: Option<S<()>>,
    pub name: S<Ident>,
    pub ty: Option<S<NodeId>>,
    pub init: Option<S<NodeId>>,
}

#[derive(Debug)]
pub struct Block {
    pub exprs: Vec<S<NodeId>>,
}

impl Block {
    pub fn empty() -> Self {
        Self {
            exprs: Vec::new(),
        }
    }
}

pub type Ident = String;

/// ```
/// [pub] mod mymod;
/// [pub] mod mymod { ... }
/// ```
#[derive(Debug)]
pub struct ModuleDecl {
    pub name: Option<ModuleName>,
    pub items: Vec<S<NodeId>>,
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
    pub ret_ty: Option<S<NodeId>>,
    pub ext_linkage: Option<S<()>>,
    pub variadic: Option<S<()>>,
    pub body: Option<S<NodeId>>,
}

#[derive(Debug)]
pub struct FnDeclArg {
    pub name: S<Ident>,
    pub ty: S<NodeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FnCallKind {
    Free,
    Method,
}

#[derive(Debug)]
pub struct FnCall {
    pub callee: S<FnCallee>,
    pub kind: FnCallKind,
    pub args: Vec<S<NodeId>>,
}

#[derive(Debug)]
pub enum FnCallee {
    Intrinsic(Intrinsic),
    Expr(NodeId),
}

#[derive(Clone, Copy, Debug)]
pub enum Intrinsic {
    OverflowingAdd,
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
    Tuple(Tuple),
}

// [<ty>; <len>]
#[derive(Debug)]
pub struct Array {
    pub ty: S<NodeId>,
    pub len: S<NodeId>,
}

// (<ty>, <ty>)
#[derive(Debug)]
pub struct Tuple {
    pub items: Vec<S<NodeId>>,
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
                ident,
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
pub struct PathItem {
    pub ident: S<Ident>,
    pub ty_args: Vec<S<NodeId>>, // TyExpr
}

#[derive(Debug)]
pub struct FieldAccess {
    pub receiver: S<NodeId>,
    pub field: S<Ident>,
}

#[derive(Debug)]
pub struct Cast {
    pub expr: S<NodeId>,
    pub ty: S<NodeId>,
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
pub struct StructDecl {
    pub name: S<Ident>,
    pub vis: Option<S<Vis>>,
    pub ty_args: Vec<S<Ident>>,
    pub fields: Vec<FieldDecl>,
}

#[derive(Debug)]
pub struct FieldDecl {
    pub name: S<Ident>,
    pub ty: S<NodeId>,
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
