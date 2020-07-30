use enum_as_inner::EnumAsInner;
use enum_map::EnumMap;
use enum_map_derive::Enum;
use slab::Slab;
use std::collections::hash_map::{Entry, HashMap};

use crate::syn::*;
use crate::syn::traverse::*;
use crate::util::EnumExt;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct PackageId(pub usize);

impl PackageId {
    pub fn null() -> Self {
        Self(usize::max_value())
    }
}

pub struct Package {
    pub name: Ident,
    pub ast: Ast,
}

pub struct Context<'a> {
    pub packages: Slab<Package>,
    pub package_by_name: HashMap<Ident, PackageId>,
    pub ast: &'a Ast,
}



#[derive(Default)]
pub struct Scope {
    pub by_name: HashMap<Ident, (Span, NodeId)>,
    pub wildcarded: Vec<NodeId>,
}

impl Scope {
    pub fn insert(&mut self, name: S<Ident>, node: NodeId) {
        match self.by_name.entry(name.value) {
            Entry::Occupied(e) => {
                let first = e.get().0;
                let this = name.span;
                eprintln!("name `{}` is defined multiple times: first at [{}:{}], redefined at [{}:{}]",
                    e.key(), first.start, first.end, this.start, this.end);
            },
            Entry::Vacant(e) => {
                e.insert((name.span, node));
            },
        }
    }

    pub fn insert_wildcarded(&mut self, node: NodeId) {
        self.wildcarded.push(node);
    }
}

#[derive(Clone, Copy, Debug, Enum)]
pub enum NsKind {
    Type,
    Value,
}

#[derive(Default)]
pub struct Names {
    scopes: EnumMap<NsKind, NodeMap<Scope>>,
    stack: Vec<(NodeId, Option<SourceId>)>,
}

impl Names {
    pub fn push(&mut self, node: NodeId, source_id: Option<SourceId>) {
        self.stack.push((node, source_id));
    }

    pub fn pop_until(&mut self, node: NodeId) {
        while self.stack.pop().unwrap().0 != node { }
    }

    pub fn resolve(&self, kind: NsKind, name: &Ident) -> Option<NodeId> {
        let scopes = &self.scopes[kind];
        for &(scope_id, _) in self.stack.iter().rev() {
            if let Some(r) = scopes.get(&scope_id)
                .and_then(|s| {
                    let r = s.by_name.get(name).map(|&(_, n)| n);
                    if !s.wildcarded.is_empty() {
                        unimplemented!();
                    }
                    r
                })
            {
                return Some(r);
            }
        }
        None
    }

    pub fn scope_for(&self, kind: NsKind, node: NodeId) -> &Scope {
        &self.scopes[kind][&node]
    }

    pub fn scope_mut(&mut self, kind: NsKind) -> &mut Scope {
        let cur = self.cur_scope();
        self.scopes[kind].entry(cur)
            .or_insert(Default::default())
    }

    pub fn print(&self, ast: &Ast) {
        for kind in NsKind::iter() {
            println!("{:?}", kind);
            let scopes = &self.scopes[kind];
            for (&n, s) in scopes {
                println!("  {:?}", ast.node_kind(n));
                for (ident, &(span, node)) in &s.by_name {
                    println!("    {:?} -> {:?}", span.spanned(ident), ast.node_kind(node));
                }
            }
        }
    }

    fn cur_scope(&self) -> NodeId {
        self.stack.last().unwrap().0
    }
}

struct MaintainNameScope<'a> {
    pub names: &'a mut Names,
}

impl AstVisitor for MaintainNameScope<'_> {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        let source_id = ctx.ast.try_module_decl(ctx.node).and_then(|m| m.source_id);
        self.names.push(ctx.node, source_id);
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        if ctx.kind != NodeKind::Let {
            self.names.pop_until(ctx.node);
        }
    }
}

pub struct DiscoverNames<'a> {
    names: MaintainNameScope<'a>,
}

impl<'a> DiscoverNames<'a> {
    pub fn new(names: &'a mut Names) -> Self {
        Self {
            names: MaintainNameScope { names },
        }
    }
}

impl AstVisitor for DiscoverNames<'_> {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        match ctx.kind {
            NodeKind::FnDecl => {
                let name = ctx.ast.fn_decl(ctx.node).name.clone();
                self.names.names.scope_mut(NsKind::Value).insert(name, ctx.node);
            },
            NodeKind::FnDeclArg => {
                let FnDeclArg { pub_name, priv_name, .. } = ctx.ast.fn_decl_arg(ctx.node);

                let _pub_name = pub_name.value.as_ref()
                    .map(|v| pub_name.span.spanned(v.clone()))
                    .unwrap_or_else(|| priv_name.clone());

                self.names.names.scope_mut(NsKind::Value).insert(priv_name.clone(), ctx.node);
            },
            NodeKind::ModuleDecl => {
                let name = &ctx.ast.module_decl(ctx.node).name;
                if let Some(name) = name {
                    self.names.names.scope_mut(NsKind::Type).insert(name.name.clone(), ctx.node);
                }
            }
            NodeKind::StructDecl => {
                let name = ctx.ast.struct_decl(ctx.node).name.clone();
                self.names.names.scope_mut(NsKind::Type).insert(name.clone(), ctx.node);
            }
            NodeKind::UsePath => {
                let UsePath { terms, .. } = ctx.ast.use_path(ctx.node);
                for term in terms {
                    match &term.value {
                        PathTerm::Ident(PathTermIdent { ident, renamed_as }) => {
                            let name = renamed_as.as_ref()
                                .unwrap_or(ident);
                            for &ns_kind in &[NsKind::Type, NsKind::Value] {
                                self.names.names.scope_mut(ns_kind).insert(name.clone(), ctx.node);
                            }
                        },
                        &PathTerm::Path(_) => {},
                        PathTerm::Star => {
                            for &ns_kind in &[NsKind::Type, NsKind::Value] {
                                self.names.names.scope_mut(ns_kind).insert_wildcarded(ctx.node);
                            }
                        },
                    }
                }
            },
            NodeKind::Let => {},
            NodeKind::LetDecl => {
                let name = ctx.ast.let_decl(ctx.node).name.clone();
                self.names.names.scope_mut(NsKind::Value).insert(name, ctx.node);
            },
            NodeKind::Block => {}
            NodeKind::BlockFlowCtl => {},
            NodeKind::Cast => {},
            NodeKind::FieldAccess => {},
            NodeKind::FnCall => {},
            NodeKind::IfExpr => {}
            NodeKind::Impl => {}
            NodeKind::Literal => {}
            NodeKind::Loop => {}
            NodeKind::Op => {}
            NodeKind::Range => {}
            NodeKind::StructType => {}
            NodeKind::StructValue => {}
            NodeKind::SymPath => {}
            NodeKind::TyExpr => {}
            NodeKind::TypeArg => {}
            NodeKind::UseStmt => {}
            NodeKind::While => {}
        }
        self.names.before_node(ctx);
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        self.names.after_node(ctx);
    }
}

pub struct ResolvedName {
    pub ns_kind: NsKind,
    pub target: NodeId,
}

#[derive(Default)]
pub struct ResolvedNames {
    names: NodeMap<ResolvedName>,
}

impl ResolvedNames {
    pub fn insert(&mut self, ns_kind: NsKind, node: NodeId, target: NodeId) {
        assert!(self.names.insert(node, ResolvedName {
            ns_kind,
            target,
        }).is_none());
    }
}

pub struct ResolveNames<'a> {
    names: MaintainNameScope<'a>,
    resolved_names: &'a mut ResolvedNames,
    ns_kind_stack: Vec<NsKind>,
}

impl<'a> ResolveNames<'a> {
    pub fn new(names: &'a mut Names, resolved_names: &'a mut ResolvedNames) -> Self {
        Self {
            names: MaintainNameScope { names },
            resolved_names,
            ns_kind_stack: Vec::new(),
        }
    }

    fn push_ns_kind(&mut self, link_kind: NodeLinkKind) {
        use NodeLinkKind::*;
        let ns_kind = match link_kind {
            | BlockExpr
            | BlockFlowCtlValue
            | Cast(CastLink::Expr)
            | FieldAccessReceiver
            | FnCall(_)
            | FnDecl(FnDeclLink::Body)
            | IfExpr(_)
            | LoopBlock
            | Op(_)
            | Range(_)
            | StructValueValue
            | TyExpr(TyExprLink::Array(ArrayLink::Len))
            | Let(LetLink::Init)
            | While(_)
            => NsKind::Value,

            | Cast(CastLink::Type)
            | FnDecl(_)
            | FnDeclArgType
            | Impl(_)
            | ModuleItem
            | Root
            | StructDecl(_)
            | StructTypeFieldType
            | SymPathTypeArg
            | TyExpr(_)
            | UsePathPath
            | UseStmtPath
            | Let(_)
            => NsKind::Type,
        };
        self.ns_kind_stack.push(ns_kind);
    }
}

impl AstVisitor for ResolveNames<'_> {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        self.names.before_node(ctx);
    }

    fn node(&mut self, ctx: AstVisitorCtx) {
        self.push_ns_kind(ctx.link_kind);

        match ctx.kind {
            NodeKind::SymPath => {
                let SymPath { anchor, items } = ctx.ast.sym_path(ctx.node);
                if anchor.is_some() {
                    unimplemented!();
                }
                let first = &items[0].ident;
                let ns_kind = *self.ns_kind_stack.last().unwrap();
                if let Some(resolved) = self.names.names.resolve(ns_kind, &first.value) {
                    if items.len() > 1 {
                        unimplemented!();
                    }
                    self.resolved_names.insert(ns_kind, ctx.node, resolved);
                } else {
                    eprintln!("[{}:{}] couldn't find name `{}` in the current scope",
                        first.span.start, first.span.end, first.value);
                }
            }
            _ => {}
        }
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        self.names.after_node(ctx);
        self.ns_kind_stack.pop().unwrap();
    }
}

#[derive(Clone, Copy, Debug)]
pub enum PrimitiveType {
    Bool,
    I32,
    Unit,
}

#[derive(Debug)]
pub struct Type {
    pub node: NodeId,
    pub data: TypeData,
}

#[derive(Debug, EnumAsInner)]
pub enum TypeData {
    Fn(FnType),
    Primitive(PrimitiveType),
    Struct(StructType),
}

#[derive(Debug)]
pub struct FnType {
    pub args: Vec<TypeId>,
    pub result: TypeId,
    pub unsafe_: bool,
    pub extern_: bool,
}

#[derive(Debug)]
pub struct StructType {
    pub fields: Vec<TypeId>,
}

#[derive(Clone, Copy, Debug, Enum)]
pub enum LangType {
    Bool,
    I32,
    Unit,
}

pub type TypeId = usize;


#[derive(Default)]
pub struct Types {
    types: Slab<Type>,
    typings: NodeMap<TypeId>,
    lang_types: EnumMap<LangType, Option<TypeId>>,
}

impl Types {
    pub fn typing_id(&self, node: NodeId) -> TypeId {
        self.typings[&node]
    }

    pub fn try_typing_id(&self, node: NodeId) -> Option<TypeId> {
        self.typings.get(&node).copied()
    }

    pub fn typing(&self, node: NodeId) -> &Type {
        &self.types[self.typing_id(node)]
    }

    pub fn insert_type(&mut self, ty: Type) -> TypeId {
        self.types.insert(ty)
    }

    pub fn insert_typing(&mut self, node: NodeId, ty: TypeId) {
        assert!(self.typings.insert(node, ty).is_none());
    }

    pub fn lang(&self, ty: LangType) -> TypeId {
        self.lang_types[ty].unwrap()
    }

    pub fn set_lang(&mut self, ty: LangType, id: TypeId) {
        assert!(self.lang_types[ty].replace(id).is_none());
    }

    pub fn instantiate(&mut self, ty_node: NodeId, ast: &Ast) -> TypeId {
        match ast.node_kind(ty_node).value {
            NodeKind::StructDecl => {
                if &ast.struct_decl(ty_node).name.value == "i32" {
                    return self.lang(LangType::I32);
                }
                unimplemented!();
            }
            _ => unimplemented!(),
        }
    }
}

pub struct TypeCheck<'a> {
    pub names: &'a ResolvedNames,
    pub types: &'a mut Types,
}

impl TypeCheck<'_> {
    pub fn build_lang_types(&mut self, names: &Names, ast: &Ast) {
        for &(n, lang, ty) in &[
            ("__unit", LangType::Unit, PrimitiveType::Unit),
            ("bool", LangType::Bool, PrimitiveType::Bool),
            ("i32", LangType::I32, PrimitiveType::I32),
        ] {
            let (_, node) = names.scope_for(NsKind::Type, ast.root).by_name[n];
            let id = self.types.insert_type(Type {
                node,
                data: TypeData::Primitive(ty),
            });
            self.types.insert_typing(node, id);
            self.types.set_lang(lang, id);
        }
    }

    fn build_type(&mut self, node: NodeId, ast: &Ast) -> TypeId {
        if let Some(ty) = self.types.try_typing_id(node) {
            ty
        } else {
            AstTraverser {
                ast,
                visitor: self,
            }.traverse_from(node);
            self.types.typing_id(node)
        }
    }
}

fn fatal(span: Span, s: impl std::fmt::Display) -> ! {
    panic!("[{}:{}] {}", span.start, span.end, s);
}

impl AstVisitor for TypeCheck<'_> {
    fn node(&mut self, ctx: AstVisitorCtx) {
        if self.types.try_typing_id(ctx.node).is_some() {
            return;
        }
        let ty = match ctx.kind {
            NodeKind::FnDecl => {
                let FnDecl {
                    args,
                    ret_ty,
                    unsafe_,
                    body,
                    .. } = ctx.ast.fn_decl(ctx.node);
                let args: Vec<_> = args.iter()
                    .copied()
                    .map(|n| self.build_type(n, ctx.ast))
                    .collect();
                let result = ret_ty.map(|n| self.build_type(n, ctx.ast))
                    .unwrap_or_else(|| self.types.lang(LangType::Unit));
                self.types.insert_type(Type {
                    node: ctx.node,
                    data: TypeData::Fn(FnType {
                        args,
                        result,
                        unsafe_: unsafe_.is_some(),
                        extern_: body.is_none(),
                    }),
                })
            }
            NodeKind::Literal => {
                match ctx.ast.literal(ctx.node) {
                    &Literal::Int(IntLiteral { ty, .. }) => {
                        if let Some(ty) = ty {
                            match ty {
                                IntTypeSuffix::I32 => self.types.lang(LangType::I32),
                                _ => unimplemented!()
                            }
                        } else {
                            // FIXME
                            self.types.lang(LangType::I32)
                        }
                    },
                    &Literal::Unit => self.types.lang(LangType::Unit),
                    _ => unimplemented!()
                }
            }
            | NodeKind::ModuleDecl
            | NodeKind::StructDecl
            | NodeKind::StructType
            | NodeKind::StructValue
            | NodeKind::FnDeclArg
            | NodeKind::TyExpr
            | NodeKind::SymPath
            | NodeKind::Block
            | NodeKind::IfExpr
            | NodeKind::Op
            | NodeKind::Let
            | NodeKind::LetDecl
            | NodeKind::FnCall
            => return,
            _ => {
                dbg!(ctx.ast.node_kind(ctx.node));
                unimplemented!();
            },
        };
        self.types.insert_typing(ctx.node, ty);
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        if self.types.try_typing_id(ctx.node).is_some() {
            return;
        }
        let ty = match ctx.kind {
            NodeKind::Block => {
                let expr = *ctx.ast.block(ctx.node).exprs.last().unwrap();
                self.types.typing_id(expr)
            }
            NodeKind::FnCall => {
                let FnCall {
                    callee,
                    kind,
                    args: actual_args,
                    .. } = ctx.ast.fn_call(ctx.node);
                let callee_ty = self.types.typing(*callee);
                if *kind != FnCallKind::Free {
                    unimplemented!();
                }
                let fn_ty = if let Some(v) = callee_ty.data.as_fn() {
                    v
                } else {
                    let span = ctx.ast.node_kind(*callee).span;
                    panic!("[{}:{}] expected function", span.start, span.end);
                };

                let formal_args = &ctx.ast.fn_decl(callee_ty.node).args;
                assert_eq!(actual_args.len(), formal_args.len());
                for (actual, formal) in actual_args
                    .iter()
                    .zip(formal_args.iter())
                {
                    if self.types.typing_id(actual.value) != self.types.typing_id(*formal) {
                        dbg!(self.types.typing(actual.value), self.types.typing(*formal));
                        dbg!(ctx.ast.node_kind(actual.value), ctx.ast.node_kind(*formal));
                        fatal(ctx.ast.node_kind(actual.value).span, "`fn`: incompatible actual and formal arg types");
                    }
                }

                fn_ty.result
            }
            NodeKind::FnDecl => {
                let FnDecl {
                    ret_ty,
                    body,
                    .. } = ctx.ast.fn_decl(ctx.node);
                let formal_ret_ty = ret_ty
                    .map(|n| self.types.typing_id(n))
                    .unwrap_or(self.types.lang(LangType::Unit));
                if let Some(body) = *body {
                    let actual_ret_ty = self.types.typing_id(body);
                    if actual_ret_ty != formal_ret_ty {
                        let span = ctx.ast.node_kind(ctx.node).span;
                        panic!("[{}:{}] `fn` actual and format return types are incompatible",
                            span.start, span.end);
                    }
                }
                self.types.lang(LangType::Unit)
            }
            NodeKind::FnDeclArg => {
                self.types.typing_id(ctx.ast.fn_decl_arg(ctx.node).ty)
            }
            NodeKind::IfExpr => {
                let &IfExpr { cond, if_true, if_false } = ctx.ast.if_expr(ctx.node);
                if !matches!(self.types.typing(cond).data, TypeData::Primitive(PrimitiveType::Bool)) {
                    let span = ctx.ast.node_kind(cond).span;
                    panic!("[{}:{}] expected bool expr", span.start, span.end);
                }
                let if_true_ty = self.types.typing_id(if_true);
                if let Some(if_false) = if_false {
                    if self.types.typing_id(if_false) != if_true_ty {
                        let span = ctx.ast.node_kind(cond).span;
                        panic!("[{}:{}] `if` arms have incompatible types", span.start, span.end);
                    }
                }
                if_true_ty
            }
            NodeKind::Let => {
                self.types.lang(LangType::Bool)
            }
            NodeKind::LetDecl => {
                let ty = ctx.ast.let_decl(ctx.node).ty.expect("unimplemented");
                self.build_type(ty, ctx.ast)
            }
            NodeKind::ModuleDecl => {
                self.types.lang(LangType::Unit)
            }
            NodeKind::Op => {
                match ctx.ast.op(ctx.node) {
                    &Op::Binary(BinaryOp { kind, left, right }) => {
                        let left_ty = self.types.typing_id(left);
                        let right_ty = self.types.typing_id(right);
                        match kind.value {
                            BinaryOpKind::LtEq => {
                                {
                                    let left_ty = &self.types.types[left_ty];
                                    let right_ty = &self.types.types[right_ty];
                                    if !matches!(left_ty.data, TypeData::Primitive(PrimitiveType::I32)) ||
                                        !matches!(right_ty.data, TypeData::Primitive(PrimitiveType::I32))
                                    {
                                        let op_span = ctx.ast.node_kind(ctx.node).span;
                                        panic!("operation `<=` at [{}:{}] is not defined for {:?} and {:?}",
                                            op_span.start, op_span.end,
                                            left_ty, right_ty);
                                    }
                                }
                                self.types.lang(LangType::Bool)
                            },
                            BinaryOpKind::Add => {
                                {
                                    let left_ty = &self.types.types[left_ty];
                                    let right_ty = &self.types.types[right_ty];
                                    if !matches!(left_ty.data, TypeData::Primitive(PrimitiveType::I32)) ||
                                        !matches!(right_ty.data, TypeData::Primitive(PrimitiveType::I32))
                                    {
                                        let op_span = ctx.ast.node_kind(ctx.node).span;
                                        panic!("operation `+` at [{}:{}] is not defined for {:?} and {:?}",
                                            op_span.start, op_span.end,
                                            left_ty, right_ty);
                                    }
                                }
                                left_ty
                            }
                            BinaryOpKind::Sub => {
                                {
                                    let left_ty = &self.types.types[left_ty];
                                    let right_ty = &self.types.types[right_ty];
                                    if !matches!(left_ty.data, TypeData::Primitive(PrimitiveType::I32)) ||
                                        !matches!(right_ty.data, TypeData::Primitive(PrimitiveType::I32))
                                    {
                                        let op_span = ctx.ast.node_kind(ctx.node).span;
                                        panic!("operation `-` at [{}:{}] is not defined for {:?} and {:?}",
                                            op_span.start, op_span.end,
                                            left_ty, right_ty);
                                    }
                                }
                                left_ty
                            }
                            _ => unimplemented!(),
                        }
                    }
                    _ => unimplemented!(),
                }
            }
            NodeKind::StructDecl => {
                // let &StructDecl { ty, .. } = ctx.ast.struct_decl(ctx.node);
                // self.types.typing_id(ty)
                // -> Unit
                unimplemented!()
            }
            NodeKind::StructType => {
                let fields = &ctx.ast.struct_type(ctx.node).fields;
                let fields: Vec<_> = fields
                    .iter()
                    .map(|f| self.build_type(f.ty, ctx.ast))
                    .collect();
                self.types.insert_type(Type {
                    node: ctx.node,
                    data: TypeData::Struct(StructType {
                        fields,
                    }),
                })
            }
            NodeKind::StructValue => {
                let StructValue { name, anonymous_fields, fields } = ctx.ast.struct_value(ctx.node);
                assert!(anonymous_fields.is_none() || !fields.is_empty());
                if name.is_some() || !fields.is_empty() {
                    unimplemented!();
                }
                self.types.lang(LangType::Unit)
            }
            NodeKind::SymPath => {
                let target = self.names.names[&ctx.node].target;
                self.build_type(target, ctx.ast)
            }
            NodeKind::TyExpr => {
                let TyExpr { muta: _, data } = ctx.ast.ty_expr(ctx.node);
                match &data.value {
                    TyData::Array(_) => unimplemented!(),
                    TyData::Ptr(_) => unimplemented!(),
                    TyData::Ref(_) => unimplemented!(),
                    TyData::Slice(_) => unimplemented!(),
                    &TyData::SymPath(node) => {
                        self.types.typing_id(node)
                    }
                    TyData::Struct(_) => unimplemented!(),
                }
            }
            _ => unimplemented!("{:?}", ctx.ast.node_kind(ctx.node))
        };
        self.types.insert_typing(ctx.node, ty);
    }
}