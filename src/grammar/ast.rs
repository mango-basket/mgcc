use crate::tokenizer::token::{Slice, Token};

#[derive(Debug)]
pub enum Ast<'ip> {
    Identifier(Token<'ip>),
    Int(Token<'ip>),
    Bool(Token<'ip>),
    Ref(Box<Ast<'ip>>),
    Deref(Box<Ast<'ip>>),
    UnaryOp {
        op: Token<'ip>,
        operand: Box<Ast<'ip>>,
    },
    BinaryOp {
        left: Box<Ast<'ip>>,
        op: Token<'ip>,
        right: Box<Ast<'ip>>,
    },
    VarDef {
        name: Token<'ip>,
        vartype: Option<Box<Ast<'ip>>>,
        rhs: Box<Ast<'ip>>,
    },
    Reassign {
        lhs: Box<Ast<'ip>>,
        rhs: Box<Ast<'ip>>,
    },
    Statements(Vec<Ast<'ip>>),
    Items(Vec<Ast<'ip>>),
    IfElse {
        condition: Box<Ast<'ip>>,
        ifbody: Box<Ast<'ip>>,
        elsebody: Option<Box<Ast<'ip>>>,
    },
    Func {
        name: Token<'ip>,
        params: Vec<(Token<'ip>, Ast<'ip>)>,
        body: Box<Ast<'ip>>,
        ret: Option<Box<Ast<'ip>>>,
    },
    Loop(Box<Ast<'ip>>),
    Break(Option<Box<Ast<'ip>>>),
    Return(Option<Box<Ast<'ip>>>),
    Continue,
    Disp(Box<Ast<'ip>>),
    FuncCall {
        name: Token<'ip>,
        params: Vec<(Token<'ip>, Ast<'ip>)>,
    },
}

impl<'ip> Ast<'ip> {
    pub fn pretty(&self, indent: usize) -> String {
        let pad = "  ".repeat(indent);
        match self {
            Ast::Identifier(tok) => format!("{}Ident({})", pad, tok.slice.get_str()),
            Ast::Int(tok) => format!("{}Int({})", pad, tok.slice.get_str()),
            Ast::Bool(tok) => format!("{}Bool({})", pad, tok.slice.get_str()),
            Ast::Ref(inner) => format!("{}Ref({})", pad, inner.pretty(0)),
            Ast::Deref(inner) => format!("{}Deref({})", pad, inner.pretty(0)),
            Ast::UnaryOp { op, operand } => {
                format!(
                    "{}UnaryOp({},{})",
                    pad,
                    op.slice.get_str(),
                    operand.pretty(0)
                )
            }
            Ast::BinaryOp { left, op, right } => {
                format!(
                    "{}BinaryOp({},{},{})",
                    pad,
                    op.slice.get_str(),
                    left.pretty(0),
                    right.pretty(0)
                )
            }
            Ast::VarDef { name, vartype, rhs } => {
                if let Some(t) = vartype {
                    format!(
                        "{}VarDef({}:{},{})",
                        pad,
                        name.slice.get_str(),
                        t.pretty(0),
                        rhs.pretty(0)
                    )
                } else {
                    format!("{}VarDef({},{})", pad, name.slice.get_str(), rhs.pretty(0))
                }
            }
            Ast::Reassign { lhs, rhs } => {
                format!("{}Reassign({}, {})", pad, lhs.pretty(0), rhs.pretty(0))
            }
            Ast::Statements(stmts) => {
                let mut s = format!("{}Statements", pad);
                for stmt in stmts {
                    s.push('\n');
                    s.push_str(&stmt.pretty(indent + 1));
                }
                s
            }
            Ast::IfElse {
                condition,
                ifbody,
                elsebody,
            } => {
                let else_str = if let Some(e) = elsebody {
                    format!(", Else({})", e.pretty(0))
                } else {
                    "".to_string()
                };
                format!(
                    "{}If({},{}){}",
                    pad,
                    condition.pretty(0),
                    ifbody.pretty(0),
                    else_str
                )
            }
            Ast::Loop(body) => format!("{}Loop({})", pad, body.pretty(0)),
            Ast::Break(expr_opt) => {
                if let Some(expr) = expr_opt {
                    format!("{}Break({})", pad, expr.pretty(0))
                } else {
                    format!("{}Break", pad)
                }
            }
            Ast::Continue => format!("{}Continue", pad),
            Ast::Disp(ast) => format!("{}Disp {}", pad, ast.pretty(0)),
            Ast::Items(stmts) => {
                let mut s = format!("{}Items", pad);
                for stmt in stmts {
                    s.push('\n');
                    s.push_str(&stmt.pretty(indent + 1));
                }
                s
            }
            Ast::Func {
                name,
                params,
                body,
                ret,
            } => {
                let params_str = params
                    .iter()
                    .map(|(n, t)| format!("{}:{}", n.slice.get_str(), t.pretty(0)))
                    .collect::<Vec<_>>()
                    .join(", ");
                let ret_str = if let Some(r) = ret {
                    format!(" -> {}", r.pretty(0))
                } else {
                    "".to_string()
                };
                format!(
                    "{}Func({}({}){} {})",
                    pad,
                    name.slice.get_str(),
                    params_str,
                    ret_str,
                    body.pretty(indent + 1)
                )
            }
            Ast::Return(expr_opt) => {
                if let Some(expr) = expr_opt {
                    format!("{}Return({})", pad, expr.pretty(0))
                } else {
                    format!("{}Return", pad)
                }
            }
            Ast::FuncCall { name, params } => {
                let params_str = params
                    .iter()
                    .map(|(n, t)| format!("{}:{}", n.slice.get_str(), t.pretty(0)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{pad}Call {} ({params_str})", name.slice.to_string())
            }
        }
    }

    pub fn get_slice(&self) -> Slice<'ip> {
        match self {
            Ast::Identifier(t) | Ast::Int(t) | Ast::Bool(t) => t.slice.clone(),
            Ast::Ref(inner) | Ast::Deref(inner) | Ast::Loop(inner) => inner.get_slice(),
            Ast::UnaryOp { op, operand } => {
                let start = op.slice.start;
                let end = operand.get_slice().start + operand.get_slice().len;
                Slice::new(start, end - start, op.slice.input)
            }
            Ast::BinaryOp { left, op, right } => {
                let start = left.get_slice().start;
                let end = right.get_slice().start + right.get_slice().len;
                Slice::new(start, end - start, op.slice.input)
            }
            Ast::VarDef {
                name,
                vartype: _,
                rhs,
            } => {
                let start = name.slice.start;
                let end = rhs.get_slice().start + rhs.get_slice().len;
                Slice::new(start, end - start, name.slice.input)
            }
            Ast::Reassign { lhs, rhs } => {
                let start = lhs.get_slice().start;
                let end = rhs.get_slice().start + rhs.get_slice().len;
                Slice::new(start, end - start, lhs.get_slice().input)
            }
            Ast::Statements(stmts) => {
                if stmts.is_empty() {
                    Slice::new(0, 0, "")
                } else {
                    let start = stmts.first().unwrap().get_slice().start;
                    let last = stmts.last().unwrap().get_slice();
                    let end = last.start + last.len;
                    Slice::new(start, end - start, last.input)
                }
            }
            Ast::IfElse {
                condition,
                ifbody,
                elsebody,
            } => {
                let start = condition.get_slice().start;
                let end = if let Some(else_ast) = elsebody {
                    let s = else_ast.get_slice();
                    s.start + s.len
                } else {
                    ifbody.get_slice().start + ifbody.get_slice().len
                };
                Slice::new(start, end - start, condition.get_slice().input)
            }
            Ast::Break(expr_opt) => {
                if let Some(expr) = expr_opt {
                    expr.get_slice()
                } else {
                    Slice::new(0, 0, "")
                }
            }
            Ast::Continue => Slice::new(0, 0, ""),
            Ast::Disp(ast) => ast.get_slice(),
            Ast::Items(items) => {
                if items.is_empty() {
                    Slice::new(0, 0, "")
                } else {
                    let start = items.first().unwrap().get_slice().start;
                    let last = items.last().unwrap().get_slice();
                    let end = last.start + last.len;
                    Slice::new(start, end - start, last.input)
                }
            }
            Ast::Func {
                name,
                params: _,
                body,
                ret,
            } => {
                let start = name.slice.start;

                // compute end position
                let end = if let Some(ret_tok) = ret {
                    ret_tok.get_slice().start + ret_tok.get_slice().len
                } else {
                    let b = body.get_slice();
                    b.start + b.len
                };

                Slice::new(start, end - start, name.slice.input)
            }
            Ast::Return(expr_opt) => {
                if let Some(expr) = expr_opt {
                    expr.get_slice()
                } else {
                    Slice::new(0, 0, "")
                }
            }
            Ast::FuncCall { name, params: _ } => name.clone().slice,
        }
    }
}
