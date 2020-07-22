use std::fmt;

use super::*;
use std::fmt::{Formatter, Write};

impl Ast {
    pub fn display(&self) -> Display {
        Display {
            ast: self,
            node: self.root.value,
        }
    }
}

pub struct Display<'a> {
    ast: &'a Ast,
    node: NodeId,
}

impl Display<'_> {
    fn node(&self, node: NodeId, in_type_pos: bool, p: &mut Printer) -> fmt::Result {
        match self.ast.node_kind(node) {
            NodeKind::Block => {
                let Block { exprs } = self.ast.block(node);
                p.print("{")?;
                p.indent()?;

                let no_result = exprs.last()
                    .map(|e| self.ast.is_empty_node(e.value)) == Some(true);
                let it = exprs.iter().enumerate()
                    .take(if no_result { exprs.len() - 1 } else { exprs.len() });
                for (i, expr) in it {
                    self.node(expr.value, false, p)?;
                    if no_result || i < exprs.len() - 1 {
                        p.println(";")?;
                    }
                }
                p.unindent()?;
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
                if let Some(value) = value {
                    p.print(' ')?;
                    self.node(value.value, false, p)?;
                }
            }
            NodeKind::Cast => {
                let Cast { expr, ty } = self.ast.cast(node);
                self.expr(expr.value, p)?;
                p.print(" as ")?;
                self.node(ty.value, true, p)?;
            }
            NodeKind::FieldAccess => {
                let FieldAccess { receiver, field } = self.ast.field_access(node);
                let excl = self.ast.try_literal(receiver.value)
                    .map(|l| l.as_int().is_some() || l.as_float().is_some())
                    == Some(true) ||
                    self.ast.try_field_access(receiver.value)
                        .map(|f| f.field.value.as_index().is_some())
                        == Some(true);
                self.expr_excl(receiver.value, excl, p)?;
                p.print('.')?;

                p.print(&field.value)?;
            }
            NodeKind::FnDecl => {
                let FnDecl {
                    name,
                    vis,
                    ty_args,
                    args,
                    ret_ty,
                    unsaf,
                    variadic,
                    body,
                } = self.ast.fn_decl(node);

                self.vis(vis, p)?;
                if unsaf.is_some() {
                    p.print_sep("unsafe")?;
                }
                p.print_sep("fn")?;
                p.print_sep(&name.value)?;

                if !ty_args.is_empty() {
                    p.print("<")?;
                    p.print_sep_seq(ty_args.iter().map(|v| &v.value), ", ")?;
                    p.print(">")?;
                }

                p.print("(")?;
                for (i, FnDeclArg { name, ty }) in args.iter().enumerate() {
                    if i > 0 {
                        p.print(", ")?;
                    }
                    p.print(&name.value)?;
                    p.print(": ")?;
                    self.node(ty.value, in_type_pos, p)?;
                    if variadic.is_some() && i == args.len() - 1 {
                        p.print(", ...")?;
                    }
                }
                p.print(")")?;

                if let Some(ret_ty) = ret_ty {
                    p.print(" -> ")?;
                    self.node(ret_ty.value, true, p)?;
                }

                if let Some(body) = body {
                    p.print(" ")?;
                    self.node(body.value, false, p)?;
                } else {
                    p.print(";")?;
                }
                p.println("")?;
            }
            NodeKind::FnCall => {
                let FnCall { callee, kind, args } = self.ast.fn_call(node);
                let mut args = args.iter();
                if *kind == FnCallKind::Method {
                    self.expr(args.next().unwrap().value, p)?;
                    p.print('.')?;
                }
                self.expr(callee.value, p)?;

                p.print('(')?;
                for (i, arg) in args.enumerate() {
                    if i > 0 {
                        p.print(", ")?;
                    }
                    self.node(arg.value, false, p)?;
                }
                p.print(')')?;

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
            NodeKind::ModuleDecl => {
                let ModuleDecl{ name, items } = self.ast.module_decl(node);
                if let Some(n) = name {
                    self.vis(&n.vis, p)?;
                    p.print_sep(&n.name.value)?;
                    p.print_sep("{")?;
                    p.indent()?;
                }
                for item in items {
                    self.node(item.value, false, p)?;
                }
                if name.is_some() {
                    p.unindent()?;
                }
            }
            NodeKind::Op => {
                let node= self.ast.op(node);
                match node {
                    Op::Binary(BinaryOp { kind, left, right }) => {
                        self.expr(left.value, p)?;

                        if kind.value == BinaryOpKind::Index {
                            p.print("[")?;
                            self.node(right.value, false, p)?;
                            p.print("]")?;
                        } else {
                            use BinaryOpKind::*;
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
                            self.expr(right.value, p)?;
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
                        self.expr(arg.value, p)?;
                        if !prefix {
                            p.print(s)?;
                        }
                    }
                }
            }
            NodeKind::Range => {
                let Range { kind, start, end } = self.ast.range(node);
                if let Some(start) = start {
                    self.expr(start.value, p)?;
                }
                match kind {
                    RangeKind::Exclusive => p.print("..")?,
                    RangeKind::Inclusive => p.print("..=")?,
                }
                if let Some(end) = end {
                    self.expr(end.value, p)?;
                }
            }
            NodeKind::StructDecl => unimplemented!(),
            NodeKind::SymPath => {
                let SymPath { anchor, items } = self.ast.sym_path(node);
                self.path_anchor(anchor.map(|v| v.value), p)?;
                let needs_parens = !in_type_pos && !items.last().unwrap().ty_args.is_empty();
                if needs_parens {
                    p.print('(')?;
                }
                for (i, PathItem { ident, ty_args }) in items.iter().enumerate() {
                    if i > 0 {
                        p.print("::")?;
                    }

                    self.ident(ident, p)?;
                    if !ty_args.is_empty() {
                        p.print("<")?;
                        for (i, v) in ty_args.iter().enumerate() {
                            if i > 0 {
                                p.print(", ")?;
                            }
                            self.node(v.value, true, p)?;
                        }
                        p.print(">")?;
                    }
                }
                if needs_parens {
                    p.print(')')?;
                }
            }
            NodeKind::Tuple => {
                let Tuple { items } = self.ast.tuple(node);
                p.print('(')?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        p.print(", ")?;
                    }
                    self.node(item.value, false, p)?;
                }
                if items.len() == 1 {
                    p.print(',')?;
                }
                p.print(')')?;
            }
            NodeKind::TyExpr => {
                let TyExpr { muta, data } = self.ast.ty_expr(node);
                if muta.is_some() {
                    p.print("mut ")?;
                }
                match &data.value {
                    TyData::Array(Array { ty, len }) => {
                        p.print("[")?;
                        self.node(ty.value, true, p)?;
                        self.node(len.value, false, p)?;
                        p.print("]")?;
                    }
                    TyData::Ptr(v) => {
                        p.print("*")?;
                        self.node(*v, true, p)?;
                    }
                    TyData::Ref(v) => {
                        p.print("&")?;
                        self.node(*v, true, p)?;
                    }
                    TyData::Slice(Slice { ty, resizable }) => {
                        p.print("[")?;
                        self.node(*ty, true, p)?;
                        if *resizable {
                            p.print("*")?;
                        }
                        p.print("]")?;
                    }
                    TyData::SymPath(v) => {
                        self.node(*v, true, p)?;
                    }
                    TyData::Tuple(Tuple { items }) => {
                        for (i, v) in items.iter().enumerate() {
                            if i > 0 {
                                p.print(", ")?;
                            }
                            self.node(v.value, true, p)?;
                        }
                    }
                }
            }
            NodeKind::UseStmt => {
                let UseStmt { vis, path } = self.ast.use_stmt(node);
                let AnchoredPath { anchor, path } = path.value;
                self.vis(vis, p)?;
                p.print_sep("use ")?;
                self.path_anchor(anchor, p)?;

                self.use_path(path, p)?;
                p.println(";")?;
            }
            NodeKind::UsePath => unimplemented!(),
            NodeKind::VarDecl => {
                let VarDecl { muta, name, ty, init } = self.ast.var_decl(node);
                p.print("let ")?;
                if muta.is_some() {
                    p.print("mut ")?;
                }
                self.ident(name, p)?;
                if let Some(ty) = ty {
                    p.print(": ")?;
                    self.node(ty.value, true, p)?;
                }
                if let Some(init) = init {
                    p.print(" = ")?;
                    self.node(init.value, false, p)?;
                }
            }
            NodeKind::Empty => {
                p.println(";")?;
            }
        }
        Ok(())
    }

    fn vis(&self, vis: &Option<S<Vis>>, p: &mut Printer) -> fmt::Result {
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

    fn path_anchor(&self, v: Option<PathAnchor>, p: &mut Printer) -> fmt::Result {
        if let Some(v) = v {
            match v {
                PathAnchor::Package => p.print("package::"),
                PathAnchor::Root => p.print("::"),
                PathAnchor::Super { count } => p.repeat("super::", count),
            }?
        }
        Ok(())
    }

    fn use_path(&self, node: NodeId, p: &mut Printer) -> fmt::Result {
        let UsePath { prefix, terms } = self.ast.use_path(node);
        for ident in prefix.iter() {
            p.print(&ident.value)?;
            p.print("::")?;
        }
        if terms.is_empty() || terms.len() > 1 {
            p.print("{")?;
        }
        if terms.len() > 1 {
            p.indent()?;
        }
        for term in terms.iter() {
            match &term.value {
                PathTerm::Ident(PathTermIdent { ident, renamed_as }) => {
                    p.print(&ident.value)?;
                    self.path_term_as(renamed_as, p)?;
                }
                PathTerm::Path(path) => {
                    self.use_path(*path, p)?;
                }
                PathTerm::Star => {
                    p.print("*")?;
                }
                PathTerm::Self_(PathTermSelf { renamed_as }) => {
                    p.print("self")?;
                    self.path_term_as(renamed_as, p)?;
                }
            }
            if terms.len() > 1 {
                p.println(",")?;
            }
        }
        if terms.len() > 1 {
            p.unindent()?;
        }
        if terms.is_empty() || terms.len() > 1 {
            p.print("}")?;
        }
        Ok(())
    }

    fn path_term_as(&self, v: &Option<S<Ident>>, p: &mut Printer) -> fmt::Result {
        if let Some(v) = v {
            p.print_sep("as")?;
            p.print_sep(&v.value)?;
        }
        Ok(())
    }

    fn ident(&self, ident: &S<Ident>, p: &mut Printer) -> fmt::Result {
        let raw = match ident.value.to_ascii_lowercase().as_str() {
            // Disambiguate for float literal tests.
            "inf" | "infinity" | "nan" => true,
            _ => ident.value.parse::<Keyword>().is_ok(),
        };

        if raw {
            p.print("r#")?;
        }

        p.print(&ident.value)
    }

    fn char(&self, c: char, escape_single_quote: bool, p: &mut Printer) -> fmt::Result {
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

    fn label(&self, l: &S<Label>, p: &mut Printer) -> fmt::Result {
        p.print(format_args!("@{}", &l.value))
    }

    fn expr(&self, node: NodeId, p: &mut Printer) -> fmt::Result {
        let no_parens = matches!(self.ast.node_kind(node),
            NodeKind::SymPath
            | NodeKind::FnCall
            | NodeKind::Literal
            | NodeKind::FieldAccess
            | NodeKind::Block);
        self.expr0(node, no_parens, p)
    }

    fn expr_excl(&self, node: NodeId, excl: bool, p: &mut Printer) -> fmt::Result {
        let no_parens = !excl && matches!(self.ast.node_kind(node),
            NodeKind::SymPath
            | NodeKind::FnCall
            | NodeKind::Literal
            | NodeKind::FieldAccess
            | NodeKind::Block);
        self.expr0(node, no_parens, p)
    }

    fn expr0(&self, node: NodeId, no_parens: bool, p: &mut Printer) -> fmt::Result {
        if !no_parens {
            p.print('(')?;
        }
        self.node(node, false, p)?;
        if !no_parens {
            p.print(')')?;
        }
        Ok(())
    }
}

struct Printer<'a, 'b: 'a> {
    f: &'a mut Formatter<'b>,
    indent: u32,
    bol: bool,
}

impl Printer<'_, '_> {
    fn println(&mut self, f: impl fmt::Display) -> fmt::Result {
        self.print(f)?;
        self.nl()
    }

    fn print(&mut self, f: impl fmt::Display) -> fmt::Result {
        self.print0(false, f)
    }

    fn print_sep(&mut self, f: impl fmt::Display) -> fmt::Result {
        self.print0(true, f)
    }

    fn print_sep_seq<D: fmt::Display, I: Iterator<Item=D>>(&mut self, it: I, sep: &str) -> fmt::Result {
        for (i, v) in it.enumerate() {
            if i > 0 {
                self.print(sep)?;
            }
            self.print(v)?;
        }
        Ok(())
    }

    fn print0(&mut self, sep: bool, f: impl fmt::Display) -> fmt::Result {
        if self.bol {
            self.repeat(' ', self.indent)?;
            self.bol = false;
        } else if sep {
            self.f.write_char(' ')?;
        }
        f.fmt(self.f)
    }

    fn nl(&mut self) -> fmt::Result {
        self.bol = true;
        self.f.write_char('\n')
    }

    fn indent(&mut self) -> fmt::Result {
        self.indent += 2;
        if !self.bol {
            self.nl()?;
        }
        Ok(())
    }

    fn unindent(&mut self) -> fmt::Result {
        self.indent -= 2;
        if !self.bol {
            self.nl()?;
        }
        Ok(())
    }

    fn repeat(&mut self, d: impl fmt::Display, count: u32) -> fmt::Result {
        for _ in 0..count {
            d.fmt(self.f)?;
        }
        Ok(())
    }
}

impl<'a> fmt::Display for Display<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.node(self.node, false, &mut Printer { f, indent: 0, bol: true, })
    }
}