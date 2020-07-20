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
                p.println("}")?;
            }
            NodeKind::Cast => unimplemented!(),
            NodeKind::FieldAccess => {
                let FieldAccess { receiver, field } = self.ast.field_access(node);
                p.print("(")?;
                self.node(receiver.value, false, p)?;
                p.print(").")?;

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
                    p.println(";")?;
                }
            }
            NodeKind::FnCall => unimplemented!(),
            NodeKind::Literal => {
                let node = self.ast.literal(node);
                match node {
                    &Literal::Bool(v) => p.print(if v { "true" } else { "false" })?,
                    Literal::Char(_) => unimplemented!(),
                    Literal::String(v) => {
                        p.print("\"")?;
                        for c in v.chars() {
                            match c {
                                '\n' => p.print(r"\n")?,
                                '\r' => p.print(r"\r")?,
                                '\t' => p.print(r"\t")?,
                                '\\' => p.print(r"\\")?,
                                '\"' => p.print(r#"\""#)?,
                                '\x00'..='\x1f' | '\x7f' => {
                                    p.print(format_args!(r"\x{:02x}", c as u8))?;
                                }
                                _ => {
                                    p.print(c)?;
                                }
                            }
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
                            p.print('.')?;
                        }
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
                    Op::BinaryOp(BinaryOp { kind, left, right }) => {
                        p.print("(")?;
                        self.node(left.value, false, p)?;
                        p.print(")")?;

                        p.print(format_args!(" {} ", kind.value))?;

                        p.print("(")?;
                        self.node(right.value, false, p)?;
                        p.print(")")?;
                    },
                    Op::Unary(UnaryOp { kind, arg }) => {
                        p.print(format_args!("{}", kind.value))?;
                        p.print("(")?;
                        self.node(arg.value, false, p)?;
                        p.print(")")?;
                    }
                }
            }
            NodeKind::StructDecl => unimplemented!(),
            NodeKind::SymPath => {
                let SymPath { anchor, items } = self.ast.sym_path(node);
                self.path_anchor(anchor.map(|v| v.value), p)?;
                for (i, PathItem { ident, ty_args }) in items.iter().enumerate() {
                    if i > 0 {
                        p.print("::")?;
                    }

                    // Disambiguate foor float literal tests.
                    match ident.value.to_ascii_lowercase().as_str() {
                        "inf" | "infinity" | "nan" =>  p.print("r#")?,
                        _ => {}
                    }

                    p.print(&ident.value)?;
                    if !ty_args.is_empty() {
                        if !in_type_pos {
                            p.print("::")?;
                        }
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
            }
            NodeKind::TyExpr => {
                let TyExpr { muta, data } = self.ast.ty_expr(node);
                if muta.is_some() {
                    p.print_sep("mut")?;
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
            NodeKind::VarDecl => unimplemented!(),
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