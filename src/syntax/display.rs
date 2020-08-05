use std::fmt::{self, Result, Write};

use super::*;

impl Ast {
    pub fn display(&self) -> Display {
        Display {
            ast: self,
            node: self.root,
        }
    }
}

pub struct Display<'a> {
    ast: &'a Ast,
    node: NodeId,
}

impl Display<'_> {
    fn node(&self, node: NodeId, at_group_level: bool, p: &mut Printer) -> Result {
        match self.ast.node_kind(node).value {
            NodeKind::Block => {
                let Block { exprs } = self.ast.block(node);
                p.print("{")?;
                if exprs.len() > 0 {
                    p.indent()?;

                    let no_result = exprs.last()
                        .and_then(|&v| self.ast.try_struct_value(v))
                        .map(|v| v.fields.is_empty()) == Some(true);
                    let it = exprs.iter().enumerate()
                        .take(if no_result { exprs.len() - 1 } else { exprs.len() });
                    for (i, &expr) in it {
                        self.node(expr, true, p)?;
                        if !crate::syntax::parse::is_item(self.ast.node_kind(expr).value)
                            && (no_result || i < exprs.len() - 1)
                        {
                            p.println(";")?;
                        }
                    }
                    p.unindent()?;
                }
                p.print("}")?;
            }
            NodeKind::BlockFlowCtl => {
                let BlockFlowCtl { kind, label, value } = self.ast.block_flow_ctl(node);
                match kind {
                    BlockFlowCtlKind::Break => p.print("break")?,
                    BlockFlowCtlKind::Continue => p.print("continue")?,
                    BlockFlowCtlKind::Return => p.print("return")?,
                }
                if let Some(label) = label {
                    p.print(' ')?;
                    self.label(label, p)?;
                }
                if let &Some(value) = value {
                    p.print(' ')?;
                    self.node(value, false, p)?;
                }
            }
            NodeKind::Cast => {
                let Cast { expr, ty } = self.ast.cast(node);
                self.expr(*expr, p)?;
                p.print(" as ")?;
                self.node(*ty, false, p)?;
            }
            NodeKind::FieldAccess => {
                let FieldAccess { receiver, field } = self.ast.field_access(node);
                let excl = self.ast.try_literal(*receiver)
                    .map(|l| l.as_int().is_some() || l.as_float().is_some())
                    == Some(true) ||
                    self.ast.try_field_access(*receiver)
                        .map(|f| f.field.value.as_index().is_some())
                        == Some(true);
                self.expr_excl(*receiver, excl, p)?;
                p.print('.')?;

                p.print(&field.value)?;
            }
            NodeKind::Fn_ => {
                let &Fn_ { decl } = self.ast.fn_(node);
                self.node(decl, at_group_level, p)?;
            }
            NodeKind::FnDecl => {
                let FnDecl {
                    name,
                    vis,
                    ty_args,
                    args,
                    ret_ty,
                    unsafe_,
                    variadic,
                    body,
                } = self.ast.fn_decl(node);

                self.vis(vis, p)?;
                if unsafe_.is_some() {
                    p.print_sep("unsafe")?;
                }
                p.print_sep("fn")?;
                p.print_sep(&name.value)?;

                self.formal_ty_args(ty_args, p)?;

                p.print("(")?;
                for (i, &arg) in args.iter().enumerate() {
                    let FnDeclArg { pub_name, priv_name, ty } = self.ast.fn_decl_arg(arg);
                    if i > 0 {
                        p.print(", ")?;
                    }
                    if let Some(pub_name) = &pub_name.value {
                        if pub_name != &priv_name.value {
                            p.print(pub_name)?;
                            p.print(' ')?;
                        }
                    } else if i > 0 {
                        p.print("_ ")?;
                    }
                    if priv_name.value.is_self_lower() {
                        let s = &mut String::new();
                        self.node(*ty, false, &mut Printer::new(s))?;
                        p.print(s.to_ascii_lowercase())?;
                    } else {
                        p.print(&priv_name.value)?;
                        p.print(": ")?;
                        self.node(*ty, false, p)?;
                    }

                    if variadic.is_some() && i == args.len() - 1 {
                        p.print(", ...")?;
                    }
                }
                p.print(")")?;

                if let &Some(ret_ty) = ret_ty {
                    p.print(" -> ")?;
                    self.node(ret_ty, false, p)?;
                }

                if let &Some(body) = body {
                    p.print(" ")?;
                    self.node(body, false, p)?;
                } else {
                    p.print(";")?;
                }
                p.println("")?;
            }
            NodeKind::FnDeclArg => unreachable!(),
            NodeKind::FnCall => {
                let FnCall { callee, kind, args } = self.ast.fn_call(node);
                let mut args = args.iter();
                if *kind == FnCallKind::Method {
                    let FnCallArg { name, value } = args.next().unwrap();
                    assert!(name.is_none());
                    self.expr(*value, p)?;
                    p.print('.')?;
                }
                self.expr(*callee, p)?;

                p.print('(')?;
                for (i, FnCallArg{ name, value }) in args.enumerate() {
                    if i > 0 {
                        p.print(", ")?;
                    }
                    if let Some(name) = name {
                        p.print(&name.value)?;
                        p.print(": ")?;
                    }
                    self.node(*value, true, p)?;
                }
                p.print(')')?;
            }
            NodeKind::IfExpr => {
                let IfExpr { cond, if_true, if_false } = self.ast.if_expr(node);
                p.print("if (")?;
                self.node(*cond, true, p)?;
                p.print(") ")?;
                self.node(*if_true, false, p)?;
                if let &Some(if_false) = if_false {
                    p.print(" else ")?;
                    self.node(if_false, false, p)?;
                }
                p.println("")?;
            }
            NodeKind::Impl => {
                let Impl {
                    ty_args,
                    trait_,
                    for_,
                    items,
                } = self.ast.impl_(node);
                p.print("impl")?;
                self.formal_ty_args(ty_args, p)?;

                p.print(' ')?;
                if let Some(trait_) = trait_ {
                    self.node(*trait_, false, p)?;
                    p.print(" for ")?;
                }

                self.node(*for_, false, p)?;

                p.println(" {")?;
                p.indent()?;

                for &item in items {
                    self.node(item, false, p)?;
                }

                p.unindent()?;
                p.println('}')?;
            }
            NodeKind::Literal => {
                let node = self.ast.literal(node);
                match node {
                    &Literal::Bool(v) => p.print(if v { "true" } else { "false" })?,
                    &Literal::Char(v) => {
                        p.print('\'')?;
                        self.char(v, true, p)?;
                        p.print('\'')?;
                    }
                    Literal::String(v) => {
                        p.print("\"")?;
                        for c in v.chars() {
                            self.char(c, false, p)?;
                        }
                        p.print("\"")?;
                    }
                    &Literal::Int(IntLiteral { value, ty }) => {
                        p.print(value)?;
                        if let Some(ty) = ty {
                            p.print(format_args!("_{}", ty))?;
                        }
                    }
                    Literal::Float(FloatLiteral { value, ty }) => {
                        let s = &value.to_string();
                        p.print(s)?;
                        if let Some(ty) = ty {
                            p.print(format_args!("_{}", ty))?;
                        } else if !s.contains('.') {
                            p.print(".0")?;
                        }
                    }
                    Literal::Unit => {
                        p.print("()")?;
                    }
                }
            }
            NodeKind::Let => {
                let &Let { decl } = self.ast.let_(node);
                self.node(decl, at_group_level, p)?;
            }
            NodeKind::LetDecl => {
                let LetDecl { mut_, name, ty, init } = self.ast.let_decl(node);
                p.print("let ")?;
                if mut_.is_some() {
                    p.print("mut ")?;
                }
                self.ident(&name.value, p)?;
                if let &Some(ty) = ty {
                    p.print(": ")?;
                    self.node(ty, false, p)?;
                }
                if let &Some(init) = init {
                    p.print(" = ")?;
                    self.node(init, false, p)?;
                }
            }
            NodeKind::Loop => {
                let Loop { block } = self.ast.loop_(node);
                p.print("loop ")?;
                self.node(*block, false, p)?;
                p.println("")?;
            }
            NodeKind::Module => {
                let Module { source_id: _, name, items } = self.ast.module(node);
                if let Some(n) = name {
                    self.vis(&n.vis, p)?;
                    p.print_sep("mod")?;
                    p.print_sep(&n.name.value)?;
                    p.print_sep("{")?;
                    p.indent()?;
                }
                for &item in items {
                    self.node(item, false, p)?;
                }
                if name.is_some() {
                    p.unindent()?;
                    p.println('}')?;
                }
            }
            NodeKind::Op => {
                let node= self.ast.op(node);
                match node {
                    Op::Binary(BinaryOp { kind, left, right }) => {
                        use BinaryOpKind::*;
                        let needs_parens = !at_group_level && match kind.value {
                            | AddAssign
                            | Assign
                            | BitAndAssign
                            | BitOrAssign
                            | BitXorAssign
                            | DivAssign
                            | RemAssign
                            | MulAssign
                            | ShlAssign
                            | ShrAssign
                            | SubAssign
                            => true,

                            | Add
                            | And
                            | BitAnd
                            | BitOr
                            | BitXor
                            | Div
                            | Eq
                            | Gt
                            | GtEq
                            | Index
                            | Lt
                            | LtEq
                            | Rem
                            | Mul
                            | NotEq
                            | Or
                            | RangeExcl
                            | RangeIncl
                            | Shl
                            | Shr
                            | Sub
                            => false,
                        };
                        if needs_parens {
                            p.print('(')?;
                        }

                        self.expr(*left, p)?;

                        if kind.value == Index {
                            p.print("[")?;
                            self.node(*right, false, p)?;
                            p.print("]")?;
                        } else {
                            let s = match kind.value {
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
                                Index => unreachable!(),
                                Lt => "<",
                                LtEq => "<=",
                                Mul => "*",
                                Rem => "%",
                                RemAssign => "%=",
                                MulAssign => "*=",
                                NotEq => "!=",
                                Or => "||",
                                RangeExcl => "..",
                                RangeIncl => "..=",
                                Shl => "<<",
                                ShlAssign => "<<=",
                                Shr => ">>",
                                ShrAssign => ">>=",
                                Sub => "-",
                                SubAssign => "-=",
                            };
                            p.print(format_args!(" {} ", s))?;
                            self.expr(*right, p)?;
                            if needs_parens {
                                p.print(')')?;
                            }
                        }
                    }
                    Op::Unary(UnaryOp { kind, arg }) => {
                        use UnaryOpKind::*;

                        let (s, prefix) = match kind.value {
                            Addr => ("&", true),
                            AddrMut => ("&mut ", true),
                            Deref => ("*", true),
                            Neg => ("-", true),
                            Not => ("!", true),
                            PanickingUnwrap => ("!", false),
                            PropagatingUnwrap => ("?", false),
                        };
                        if prefix {
                            p.print(s)?;
                        }
                        self.expr(*arg, p)?;
                        if !prefix {
                            p.print(s)?;
                        }
                    }
                }
            }
            NodeKind::Path => {
                self.path(node, p)?;
            }
            | NodeKind::PathEndEmpty
            | NodeKind::PathEndIdent
            | NodeKind::PathEndStar
            | NodeKind::PathSegment
            => unreachable!("{:?}", self.ast.node_kind(node)),
            NodeKind::Range => {
                let Range { kind, start, end } = self.ast.range(node);
                if let Some(start) = start {
                    self.expr(*start, p)?;
                }
                match kind {
                    RangeKind::Exclusive => p.print("..")?,
                    RangeKind::Inclusive => p.print("..=")?,
                }
                if let Some(end) = end {
                    self.expr(*end, p)?;
                }
            }
            NodeKind::Struct => {
                let Struct { vis, name, ty_args, ty } = self.ast.struct_(node);
                self.vis(vis, p)?;
                p.print_sep("struct ")?;
                p.print(&name.value)?;
                self.formal_ty_args(ty_args, p)?;
                p.print(' ')?;
                self.struct_type(*ty, false, p)?;
                p.println("")?;
            }
            NodeKind::StructType => {
                unreachable!();
            }
            NodeKind::StructValue => {
                let StructValue {
                    name,
                    anonymous_fields,
                    fields } = self.ast.struct_value(node);
                if let &Some(name) = name {
                    self.node(name, false, p)?;
                    p.print(' ')?;
                }
                p.print('{')?;
                if !fields.is_empty() {
                    p.print(' ')?;
                    if anonymous_fields.is_some() {
                        p.print("0: ")?;
                    }
                    for (i, StructValueField { name, value }) in fields.iter().enumerate() {
                        if i > 0 {
                            p.print(", ")?;
                        }
                        if let Some(name) = name {
                            p.print(&name.value)?;
                            p.print(": ")?;
                        }
                        self.node(*value, false, p)?;
                    }
                    if name.is_none() && fields.len() == 1 {
                        p.print(',')?;
                    }

                    p.print(' ')?;
                } else {
                    p.print("/*{,}*/")?;
                }
                p.print('}')?;
            }
            NodeKind::TyExpr => {
                let TyExpr { muta, data } = self.ast.ty_expr(node);
                if muta.is_some() {
                    p.print("mut ")?;
                }
                match &data.value {
                    &TyData::Array(Array { ty, len }) => {
                        p.print("[")?;
                        self.node(ty, false, p)?;
                        self.node(len, false, p)?;
                        p.print("]")?;
                    }
                    &TyData::Ptr(v) => {
                        p.print("*")?;
                        self.node(v, false, p)?;
                    }
                    &TyData::Ref(v) => {
                        p.print("&")?;
                        self.node(v, false, p)?;
                    }
                    &TyData::Slice(Slice { ty, resizable }) => {
                        p.print("[")?;
                        self.node(ty, false, p)?;
                        if resizable {
                            p.print("*")?;
                        }
                        p.print("]")?;
                    }
                    &TyData::Path(v) => {
                        self.node(v, false, p)?;
                    }
                    &TyData::Struct(v) => {
                        self.struct_type(v, true, p)?;
                    }
                }
            }
            NodeKind::TypeArg => unreachable!(),
            NodeKind::UseStmt => {
                let UseStmt { vis, path } = self.ast.use_stmt(node);
                self.vis(vis, p)?;
                p.print_sep("use ")?;
                self.path(*path, p)?;
                p.println(";")?;
            }
            NodeKind::While => {
                let While { cond, block } = self.ast.while_(node);
                p.print("while (")?;
                self.node(*cond, true, p)?;
                p.print(") ")?;
                self.node(*block, false, p)?;
                p.println("")?;
            }
        }
        Ok(())
    }

    fn vis(&self, vis: &Option<S<Vis>>, p: &mut Printer) -> Result {
        if let Some(vis) = vis {
            p.print("pub")?;
            if let Some(r) = &vis.value.restrict {
                match &r.value {
                    VisRestrict::InPackage => {
                        p.print(format_args!("({})", "in package"))?;
                    }
                }
            }
        }
        Ok(())
    }

    fn path(&self, node: NodeId, p: &mut Printer) -> Result {
        let Path { anchor, segment } = self.ast.path(node);
        if let Some(anchor) = anchor {
            match anchor.value {
                PathAnchor::Package => p.print("package::"),
                PathAnchor::Root => p.print("::"),
                PathAnchor::Super { count } => p.repeat("super::", count),
            }?
        }
        self.path_segment(*segment, p)
    }

    fn path_item(&self, item: &PathItem, p: &mut Printer) -> Result {
        let PathItem { ident, ty_args } = item;
        self.ident(&ident.value, p)?;
        if !ty_args.is_empty() {
            p.print("<")?;
            for (i, v) in ty_args.iter().enumerate() {
                if i > 0 {
                    p.print(", ")?;
                }
                self.node(*v, false, p)?;
            }
            p.print(">")?;
        }
        Ok(())
    }

    fn path_segment(&self, node: NodeId, p: &mut Printer) -> Result {
        let PathSegment { prefix, suffix } = self.ast.path_segment(node);
        for item in prefix {
            self.path_item(item, p)?;
            p.print("::")?;
        }
        if suffix.len() > 1 {
            p.print('{')?;
        }
        if suffix.len() > 1 {
            p.indent()?;
        }
        for &next in suffix.iter() {
            self.path_suffix(next, p)?;
            if suffix.len() > 1 {
                p.println(',')?;
            }
        }
        if suffix.len() > 1 {
            p.unindent()?;
        }
        if suffix.len() > 1 {
            p.print('}')?;
        }
        Ok(())
    }

    fn path_suffix(&self, node: NodeId, p: &mut Printer) -> Result {
        match self.ast.node_kind(node).value {
            NodeKind::PathEndIdent => {
                let PathEndIdent { item, renamed_as } = self.ast.path_end_ident(node);
                self.path_item(item, p)?;
                if let Some(renamed_as) = renamed_as {
                    p.print_sep("as")?;
                    p.print_sep(&renamed_as.value)?;
                }
            }
            NodeKind::PathEndEmpty => p.print("{}")?,
            NodeKind::PathEndStar => p.print('*')?,
            NodeKind::PathSegment => self.path_segment(node, p)?,
            _ => unreachable!(),
        }
        Ok(())
    }

    fn ident(&self, ident: &Ident, p: &mut Printer) -> Result {
        let raw = match ident.to_ascii_lowercase().as_str() {
            // Disambiguate for float literal tests.
            "inf" | "infinity" | "nan" => true,
            _ => false,
        };

        if raw {
            p.print("r#")?;
        }

        p.print(ident)
    }

    fn char(&self, c: char, escape_single_quote: bool, p: &mut Printer) -> Result {
        match c {
            '\n' => p.print(r"\n"),
            '\r' => p.print(r"\r"),
            '\t' => p.print(r"\t"),
            '\\' => p.print(r"\\"),
            '\'' if escape_single_quote => p.print(r#"\'"#),
            '\"' if !escape_single_quote => p.print(r#"\""#),
            '\x00'..='\x1f' | '\x7f' => {
                p.print(format_args!(r"\x{:02x}", c as u8))
            }
            _ => {
                p.print(c)
            }
        }
    }

    fn label(&self, l: &S<Label>, p: &mut Printer) -> Result {
        p.print(format_args!("@{}", &l.value))
    }

    fn expr(&self, node: NodeId, p: &mut Printer) -> Result {
        self.expr_excl(node, false, p)
    }

    fn expr_excl(&self, node: NodeId, excl: bool, p: &mut Printer) -> Result {
        let no_parens = !excl && matches!(self.ast.node_kind(node).value,
            NodeKind::Block
            | NodeKind::FieldAccess
            | NodeKind::FnCall
            | NodeKind::IfExpr
            | NodeKind::Literal
            | NodeKind::Loop
            | NodeKind::Path
            | NodeKind::While
        );
        self.expr0(node, no_parens, p)
    }

    fn expr0(&self, node: NodeId, no_parens: bool, p: &mut Printer) -> Result {
        if !no_parens {
            p.print('(')?;
        }
        self.node(node, !no_parens, p)?;
        if !no_parens {
            p.print(')')?;
        }
        Ok(())
    }

    fn formal_ty_args(&self, ty_args: &[NodeId], p: &mut Printer) -> Result {
        if !ty_args.is_empty() {
            p.print("<")?;
            p.print_sep_seq(ty_args.iter().map(|&v| &self.ast.type_arg(v).name.value), ", ")?;
            p.print(">")?;
        }
        Ok(())
    }

    fn struct_type(&self, node: NodeId, inline: bool, p: &mut Printer) -> Result {
        let StructType { fields } = self.ast.struct_type(node);
        p.print('{')?;
        if !inline {
            p.indent()?;
        }
        let named_fields = fields.first().map(|v| v.name.is_some()).unwrap_or(false);
        if inline && named_fields {
            p.print(' ')?;
        }
        let delim = if inline { ", " } else { "," };
        for (i, StructTypeField { vis, name, ty }) in fields.iter().enumerate() {
            self.vis(vis, p)?;
            if vis.is_some() {
                p.print(' ')?;
            }
            if let Some(name) = name {
                p.print(&name.value)?;
                p.print(": ")?;
            }
            self.node(*ty, false, p)?;
            if !inline || i < fields.len() - 1 || !inline && fields.len() == 1 {
                p.print(delim)?;
                if !inline {
                    p.println("")?;
                }
            } else if inline && fields.len() == 1 {
                p.print(',')?;
            }
        }
        if inline && named_fields {
            p.print(' ')?;
        }
        if !inline {
            p.unindent()?;
        }
        p.print('}')
    }
}

struct Printer<'a> {
    w: &'a mut dyn Write,
    indent: u32,
    bol: bool,
}

impl<'a> Printer<'a> {
    fn new(w: &'a mut dyn Write) -> Self {
        Self {
            w,
            indent: 0,
            bol: true,
        }
    }

    fn println(&mut self, f: impl fmt::Display) -> Result {
        self.print(f)?;
        self.nl()
    }

    fn print(&mut self, f: impl fmt::Display) -> Result {
        self.print0(false, f)
    }

    fn print_sep(&mut self, f: impl fmt::Display) -> Result {
        self.print0(true, f)
    }

    fn print_sep_seq<D: fmt::Display, I: Iterator<Item=D>>(&mut self, it: I, sep: &str) -> Result {
        for (i, v) in it.enumerate() {
            if i > 0 {
                self.print(sep)?;
            }
            self.print(v)?;
        }
        Ok(())
    }

    fn print0(&mut self, sep: bool, f: impl fmt::Display) -> Result {
        if self.bol {
            self.repeat(' ', self.indent)?;
            self.bol = false;
        } else if sep {
            self.w.write_char(' ')?;
        }
        write!(self.w, "{}", f)
    }

    fn nl(&mut self) -> Result {
        self.bol = true;
        self.w.write_char('\n')
    }

    fn indent(&mut self) -> Result {
        self.indent += 2;
        if !self.bol {
            self.nl()?;
        }
        Ok(())
    }

    fn unindent(&mut self) -> Result {
        self.indent -= 2;
        if !self.bol {
            self.nl()?;
        }
        Ok(())
    }

    fn repeat(&mut self, d: impl fmt::Display, count: u32) -> Result {
        for _ in 0..count {
            write!(self.w, "{}", d)?;
        }
        Ok(())
    }
}

impl<'a> fmt::Display for Display<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result {
        self.node(self.node, false, &mut Printer::new(f))
    }
}