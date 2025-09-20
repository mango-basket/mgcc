use crate::tokenizer::token::{RawSlice, Token, TokenKind};

#[derive(Debug, Clone)]
pub struct AstNode<'ip> {
    pub kind: AstKind<'ip>,
    pub slice: RawSlice<'ip>,
}

impl<'ip> AstNode<'ip> {
    pub fn new(kind: AstKind<'ip>, slice: RawSlice<'ip>) -> AstNode<'ip> {
        AstNode { kind, slice }
    }
}

#[derive(Debug, Clone)]
pub enum AstKind<'ip> {
    Identifier(TokenKind),
    Int(TokenKind),
    Bool(TokenKind),
    Ref(Box<AstNode<'ip>>),
    Deref(Box<AstNode<'ip>>),
    UnaryOp {
        op: Token<'ip>,
        operand: Box<AstNode<'ip>>,
    },
    BinaryOp {
        left: Box<AstNode<'ip>>,
        op: Token<'ip>,
        right: Box<AstNode<'ip>>,
    },
    VarDef {
        name: Token<'ip>,
        vartype: Option<Box<AstNode<'ip>>>,
        rhs: Box<AstNode<'ip>>,
    },
    Reassign {
        lhs: Box<AstNode<'ip>>,
        rhs: Box<AstNode<'ip>>,
    },
    Statements(Vec<AstNode<'ip>>),
    Items(Vec<AstNode<'ip>>),
    IfElse {
        condition: Box<AstNode<'ip>>,
        ifbody: Box<AstNode<'ip>>,
        elsebody: Option<Box<AstNode<'ip>>>,
    },
    Func {
        name: Token<'ip>,
        params: Vec<(Token<'ip>, AstNode<'ip>)>,
        body: Box<AstNode<'ip>>,
        ret: Option<Box<AstNode<'ip>>>,
    },
    Loop(Box<AstNode<'ip>>),
    Break(Option<Box<AstNode<'ip>>>),
    Return(Option<Box<AstNode<'ip>>>),
    Continue,
    Disp(Box<AstNode<'ip>>),
    FuncCall {
        name: Token<'ip>,
        args: Vec<AstNode<'ip>>,
    },
}

impl<'ip> AstNode<'ip> {
    pub fn pretty(&self, indent: usize) -> String {
        let pad = "  ".repeat(indent);
        match &self.kind {
            AstKind::Identifier(_) => format!("{}Ident({})", pad, self.slice.get_str()),
            AstKind::Int(_) => format!("{}Int({})", pad, self.slice.get_str()),
            AstKind::Bool(_) => format!("{}Bool({})", pad, self.slice.get_str()),
            AstKind::Ref(inner) => format!("{}Ref({})", pad, inner.pretty(0)),
            AstKind::Deref(inner) => format!("{}Deref({})", pad, inner.pretty(0)),
            AstKind::UnaryOp { op, operand } => {
                format!(
                    "{}UnaryOp({},{})",
                    pad,
                    op.slice.get_str(),
                    operand.pretty(0)
                )
            }
            AstKind::BinaryOp { left, op, right } => {
                format!(
                    "{}BinaryOp({},{},{})",
                    pad,
                    op.slice.get_str(),
                    left.pretty(0),
                    right.pretty(0)
                )
            }
            AstKind::VarDef { name, vartype, rhs } => {
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
            AstKind::Reassign { lhs, rhs } => {
                format!("{}Reassign({}, {})", pad, lhs.pretty(0), rhs.pretty(0))
            }
            AstKind::Statements(stmts) => {
                let mut s = format!("{}Statements", pad);
                for stmt in stmts {
                    s.push('\n');
                    s.push_str(&stmt.pretty(indent + 1));
                }
                s
            }
            AstKind::IfElse {
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
            AstKind::Loop(body) => format!("{}Loop({})", pad, body.pretty(0)),
            AstKind::Break(expr_opt) => {
                if let Some(expr) = expr_opt {
                    format!("{}Break({})", pad, expr.pretty(0))
                } else {
                    format!("{}Break", pad)
                }
            }
            AstKind::Continue => format!("{}Continue", pad),
            AstKind::Disp(ast) => format!("{}Disp {}", pad, ast.pretty(0)),
            AstKind::Items(stmts) => {
                let mut s = format!("{}Items", pad);
                for stmt in stmts {
                    s.push('\n');
                    s.push_str(&stmt.pretty(indent + 1));
                }
                s
            }
            AstKind::Func {
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
            AstKind::Return(expr_opt) => {
                if let Some(expr) = expr_opt {
                    format!("{}Return({})", pad, expr.pretty(0))
                } else {
                    format!("{}Return", pad)
                }
            }
            AstKind::FuncCall { name, args: params } => {
                let params_str = params
                    .iter()
                    .map(|n| format!("{}", n.pretty(0)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{pad}Call {} ({params_str})", name.slice.to_string())
            }
        }
    }

    pub fn get_slice(&self) -> RawSlice<'ip> {
        self.slice.clone()
    }
}
