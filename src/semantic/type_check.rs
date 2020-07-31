use enum_as_inner::EnumAsInner;
use enum_map::EnumMap;
use enum_map_derive::Enum;
use slab::Slab;

use crate::syntax::*;
use crate::syntax::traverse::*;

use super::discover_names::{Names, NsKind};
use super::resolve_names::ResolvedNames;

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
            let node = names.scope(NsKind::Type, ast.root).by_name[n].node;
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
                    &Literal::Bool(_) => self.types.lang(LangType::Bool),
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
            | NodeKind::Path
            | NodeKind::PathSegment
            | NodeKind::PathEndIdent
            | NodeKind::Block
            | NodeKind::IfExpr
            | NodeKind::Op
            | NodeKind::Let
            | NodeKind::LetDecl
            | NodeKind::FnCall
            | NodeKind::Fn_
            => return,
            _ => {
                unimplemented!("{:?}", ctx.ast.node_kind(ctx.node));
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
            NodeKind::Fn_ => {
                let &Fn_ { decl } = ctx.ast.fn_(ctx.node);
                let FnDecl {
                    ret_ty,
                    body,
                    .. } = ctx.ast.fn_decl(decl);
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
            NodeKind::FnDecl => {
                unreachable!()
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
            NodeKind::Path => {
                self.types.typing_id(ctx.ast.path(ctx.node).segment)
            }
            NodeKind::PathEndIdent => {
                let target = self.names.get(ctx.node).target;
                // Ignore 'use'.
                if ctx.ast.node_kind(target).value != NodeKind::ModuleDecl {
                    self.build_type(target, ctx.ast)
                } else {
                    self.types.lang(LangType::Unit)
                }
            }
            NodeKind::PathSegment => {
                if let Some(&suffix) = ctx.ast.path_segment(ctx.node).suffix.first() {
                    self.types.typing_id(suffix)
                } else {
                    self.types.lang(LangType::Unit)
                }
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