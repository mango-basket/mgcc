use crate::{
    semantic::type_check::Type,
    tokenizer::token::{Span, Token, TokenKind},
};

#[derive(Debug, Clone, PartialEq)]
pub enum RetStatus {
    Always(Type),
    Maybe(Type),
    Never,
}

pub type TypedAstKind<'ip> = GenericAstKind<'ip, TypedAstNode<'ip>>;

#[derive(Debug)]
pub struct TypedAstNode<'ip> {
    pub kind: TypedAstKind<'ip>,
    pub span: Span<'ip>,
    pub eval_ty: Type,
    pub ret: RetStatus,
}

impl<'ip> TypedAstNode<'ip> {
    pub fn get_span(&self) -> Span<'ip> {
        self.span.clone()
    }

    pub fn from_ast(ast: &AstNode<'ip>, eval_ty: Type, ret: RetStatus) -> Self {
        fn map_children<'ip>(
            ast_kind: &AstKind<'ip>,
            eval_ty: Type,
            ret: RetStatus,
        ) -> TypedAstKind<'ip> {
            match ast_kind {
                AstKind::Identifier(t) => TypedAstKind::Identifier(t.clone()),
                AstKind::Int(t) => TypedAstKind::Int(t.clone()),
                AstKind::Bool(t) => TypedAstKind::Bool(t.clone()),
                AstKind::Ref(inner) => TypedAstKind::Ref(Box::new(TypedAstNode::from_ast(
                    inner,
                    eval_ty.clone(),
                    ret.clone(),
                ))),
                AstKind::Deref(inner) => TypedAstKind::Deref(Box::new(TypedAstNode::from_ast(
                    inner,
                    eval_ty.clone(),
                    ret.clone(),
                ))),
                AstKind::UnaryOp { op, operand } => TypedAstKind::UnaryOp {
                    op: op.clone(),
                    operand: Box::new(TypedAstNode::from_ast(
                        operand,
                        eval_ty.clone(),
                        ret.clone(),
                    )),
                },
                AstKind::BinaryOp { left, op, right } => TypedAstKind::BinaryOp {
                    left: Box::new(TypedAstNode::from_ast(left, eval_ty.clone(), ret.clone())),
                    op: op.clone(),
                    right: Box::new(TypedAstNode::from_ast(right, eval_ty.clone(), ret.clone())),
                },
                AstKind::VarDef { name, vartype, rhs } => TypedAstKind::VarDef {
                    name: name.clone(),
                    vartype: vartype
                        .as_ref()
                        .map(|v| Box::new(TypedAstNode::from_ast(v, eval_ty.clone(), ret.clone()))),
                    rhs: Box::new(TypedAstNode::from_ast(rhs, eval_ty.clone(), ret.clone())),
                },
                AstKind::Reassign { lhs, rhs } => TypedAstKind::Reassign {
                    lhs: Box::new(TypedAstNode::from_ast(lhs, eval_ty.clone(), ret.clone())),
                    rhs: Box::new(TypedAstNode::from_ast(rhs, eval_ty.clone(), ret.clone())),
                },
                AstKind::Statements(stmts) => TypedAstKind::Statements(
                    stmts
                        .iter()
                        .map(|c| TypedAstNode::from_ast(c, eval_ty.clone(), ret.clone()))
                        .collect(),
                ),
                AstKind::Items(items) => TypedAstKind::Items(
                    items
                        .iter()
                        .map(|c| TypedAstNode::from_ast(c, eval_ty.clone(), ret.clone()))
                        .collect(),
                ),
                AstKind::IfElse {
                    condition,
                    ifbody,
                    elsebody,
                } => TypedAstKind::IfElse {
                    condition: Box::new(TypedAstNode::from_ast(
                        condition,
                        eval_ty.clone(),
                        ret.clone(),
                    )),
                    ifbody: Box::new(TypedAstNode::from_ast(ifbody, eval_ty.clone(), ret.clone())),
                    elsebody: elsebody
                        .as_ref()
                        .map(|c| Box::new(TypedAstNode::from_ast(c, eval_ty.clone(), ret.clone()))),
                },
                AstKind::Func {
                    name,
                    params,
                    body,
                    ret: ret_node,
                } => TypedAstKind::Func {
                    name: name.clone(),
                    params: params
                        .iter()
                        .map(|(t, n)| {
                            (
                                t.clone(),
                                TypedAstNode::from_ast(n, eval_ty.clone(), ret.clone()),
                            )
                        })
                        .collect(),
                    body: Box::new(TypedAstNode::from_ast(body, eval_ty.clone(), ret.clone())),
                    ret: ret_node
                        .as_ref()
                        .map(|r| Box::new(TypedAstNode::from_ast(r, eval_ty.clone(), ret.clone()))),
                },
                AstKind::Loop(inner) => TypedAstKind::Loop(Box::new(TypedAstNode::from_ast(
                    inner,
                    eval_ty.clone(),
                    ret.clone(),
                ))),
                AstKind::Break(expr) => TypedAstKind::Break(
                    expr.as_ref()
                        .map(|e| Box::new(TypedAstNode::from_ast(e, eval_ty.clone(), ret.clone()))),
                ),
                AstKind::Return(expr) => TypedAstKind::Return(
                    expr.as_ref()
                        .map(|e| Box::new(TypedAstNode::from_ast(e, eval_ty.clone(), ret.clone()))),
                ),
                AstKind::Continue => TypedAstKind::Continue,
                AstKind::Disp(inner) => TypedAstKind::Disp(Box::new(TypedAstNode::from_ast(
                    inner,
                    eval_ty.clone(),
                    ret.clone(),
                ))),
                AstKind::FuncCall { name, args } => TypedAstKind::FuncCall {
                    name: name.clone(),
                    args: args
                        .iter()
                        .map(|c| TypedAstNode::from_ast(c, eval_ty.clone(), ret.clone()))
                        .collect(),
                },
                AstKind::As { lhs, rhs } => TypedAstKind::As {
                    lhs: Box::new(TypedAstNode::from_ast(lhs, eval_ty.clone(), ret.clone())),
                    rhs: rhs.clone(),
                },
                AstKind::Char(ch) => TypedAstKind::Char(ch.clone()),
            }
        }

        TypedAstNode {
            kind: map_children(&ast.kind, eval_ty.clone(), ret.clone()),
            span: ast.span.clone(),
            eval_ty,
            ret,
        }
    }
}

pub type AstKind<'ip> = GenericAstKind<'ip, AstNode<'ip>>;

#[derive(Debug, Clone)]
pub struct AstNode<'ip> {
    pub kind: AstKind<'ip>,
    pub span: Span<'ip>,
}

impl<'ip> AstNode<'ip> {
    pub fn new(kind: AstKind<'ip>, span: Span<'ip>) -> AstNode<'ip> {
        AstNode { kind, span }
    }
}

#[derive(Debug, Clone)]
pub enum GenericAstKind<'ip, Child> {
    Identifier(TokenKind),
    Int(TokenKind),
    Bool(TokenKind),
    Char(TokenKind),
    Ref(Box<Child>),
    Deref(Box<Child>),
    UnaryOp {
        op: Token<'ip>,
        operand: Box<Child>,
    },
    BinaryOp {
        left: Box<Child>,
        op: Token<'ip>,
        right: Box<Child>,
    },
    VarDef {
        name: Token<'ip>,
        vartype: Option<Box<Child>>,
        rhs: Box<Child>,
    },
    Reassign {
        lhs: Box<Child>,
        rhs: Box<Child>,
    },
    Statements(Vec<Child>),
    Items(Vec<Child>),
    IfElse {
        condition: Box<Child>,
        ifbody: Box<Child>,
        elsebody: Option<Box<Child>>,
    },
    Func {
        name: Token<'ip>,
        params: Vec<(Token<'ip>, Child)>,
        body: Box<Child>,
        ret: Option<Box<Child>>,
    },
    Loop(Box<Child>),
    Break(Option<Box<Child>>),
    Return(Option<Box<Child>>),
    Continue,
    Disp(Box<Child>),
    FuncCall {
        name: Token<'ip>,
        args: Vec<Child>,
    },
    As {
        lhs: Box<Child>,
        rhs: Token<'ip>,
    },
}

impl<'ip, Child> GenericAstKind<'ip, Child> {
    pub fn is_leaf(&self) -> bool {
        use GenericAstKind::*;

        match self {
            Identifier(_) | Int(_) | Bool(_) | Char(_) => true,
            Ref(_) => false,
            Deref(_) => false,
            UnaryOp { .. } => false,
            BinaryOp { .. } => false,
            VarDef { .. } => false,
            Reassign { .. } => false,
            Statements(_) => false,
            Items(_) => false,
            IfElse { .. } => false,
            Func { .. } => false,
            Loop(_) => false,
            Break(_) => false,
            Return(_) => false,
            Continue => false,
            Disp(_) => false,
            FuncCall { .. } => false,
            As { .. } => false,
        }
    }
}

impl<'ip> AstNode<'ip> {
    pub fn pretty(&self, indent: usize) -> String {
        let pad = "  ".repeat(indent);
        match &self.kind {
            AstKind::Identifier(_) => format!("{}Ident({})", pad, self.span.get_str()),
            AstKind::Int(_) => format!("{}Int({})", pad, self.span.get_str()),
            AstKind::Bool(_) => format!("{}Bool({})", pad, self.span.get_str()),
            AstKind::Char(_) => format!("{}Char({})", pad, self.span.get_str()),
            AstKind::Ref(inner) => format!("{}Ref({})", pad, inner.pretty(0)),
            AstKind::Deref(inner) => format!("{}Deref({})", pad, inner.pretty(0)),
            AstKind::UnaryOp { op, operand } => {
                format!(
                    "{}UnaryOp({},{})",
                    pad,
                    op.span.get_str(),
                    operand.pretty(0)
                )
            }
            AstKind::BinaryOp { left, op, right } => {
                format!(
                    "{}BinaryOp({},{},{})",
                    pad,
                    op.span.get_str(),
                    left.pretty(0),
                    right.pretty(0)
                )
            }
            AstKind::VarDef { name, vartype, rhs } => {
                if let Some(t) = vartype {
                    format!(
                        "{}VarDef({}:{},{})",
                        pad,
                        name.span.get_str(),
                        t.pretty(0),
                        rhs.pretty(0)
                    )
                } else {
                    format!("{}VarDef({},{})", pad, name.span.get_str(), rhs.pretty(0))
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
                    .map(|(n, t)| format!("{}:{}", n.span.get_str(), t.pretty(0)))
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
                    name.span.get_str(),
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
                format!("{pad}Call {} ({params_str})", name.span.to_string())
            }
            GenericAstKind::As { lhs, rhs } => {
                format!("{pad}{} as {}", lhs.pretty(0), rhs.span.get_str())
            }
        }
    }

    pub fn get_slice(&self) -> Span<'ip> {
        self.span.clone()
    }
}
