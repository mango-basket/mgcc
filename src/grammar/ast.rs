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

#[derive(Debug, Clone)]
pub enum TypedAstKind<'ip> {
    Identifier(TokenKind),
    Int(TokenKind),
    Bool(TokenKind),
    Char(TokenKind),
    Ref(Box<TypedAstNode<'ip>>),
    Deref(Box<TypedAstNode<'ip>>),
    UnaryOp {
        op: Token<'ip>,
        operand: Box<TypedAstNode<'ip>>,
    },
    BinaryOp {
        left: Box<TypedAstNode<'ip>>,
        op: Token<'ip>,
        right: Box<TypedAstNode<'ip>>,
    },
    VarDef {
        name: Token<'ip>,
        rhs: Box<TypedAstNode<'ip>>,
    },
    Reassign {
        lhs: Box<TypedAstNode<'ip>>,
        rhs: Box<TypedAstNode<'ip>>,
    },
    UpdateAssign {
        lhs: Box<TypedAstNode<'ip>>,
        op: Token<'ip>,
        rhs: Box<TypedAstNode<'ip>>,
    },
    Statements(Vec<TypedAstNode<'ip>>),
    Items(Vec<TypedAstNode<'ip>>),
    IfElse {
        condition: Box<TypedAstNode<'ip>>,
        ifbody: Box<TypedAstNode<'ip>>,
        elsebody: Option<Box<TypedAstNode<'ip>>>,
    },
    Func {
        name: Token<'ip>,
        body: Box<TypedAstNode<'ip>>,
    },
    Loop(Box<TypedAstNode<'ip>>),
    While {
        cond: Box<TypedAstNode<'ip>>,
        body: Box<TypedAstNode<'ip>>,
    },
    Break(Option<Box<TypedAstNode<'ip>>>),
    Return(Option<Box<TypedAstNode<'ip>>>),
    Continue,
    Disp(Box<TypedAstNode<'ip>>),
    FuncCall {
        name: Token<'ip>,
        args: Vec<TypedAstNode<'ip>>,
    },
    As {
        lhs: Box<TypedAstNode<'ip>>,
        rhs: Type,
    },
    Index {
        lhs: Box<TypedAstNode<'ip>>,
        rhs: Box<TypedAstNode<'ip>>,
    },
    Array(Vec<TypedAstNode<'ip>>),
    ArrayDef {
        size: Token<'ip>,
        ty: Type,
    },
    String(TokenKind), // var a[4];
    Breakpoint,
}

#[derive(Debug, Clone)]
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

    pub fn new(
        kind: TypedAstKind<'ip>,
        span: Span<'ip>,
        eval_ty: Type,
        ret: RetStatus,
    ) -> TypedAstNode<'ip> {
        TypedAstNode {
            kind,
            span,
            eval_ty,
            ret,
        }
    }

    // pub fn from_ast(ast: &AstNode<'ip>, eval_ty: Type, ret: RetStatus) -> Self {
    //     fn map_children<'ip>(
    //         ast_kind: &AstKind<'ip>,
    //         eval_ty: Type,
    //         ret: RetStatus,
    //     ) -> TypedAstKind<'ip> {
    //         match ast_kind {
    //             AstKind::Identifier(t) => TypedAstKind::Identifier(t.clone()),
    //             AstKind::Int(t) => TypedAstKind::Int(t.clone()),
    //             AstKind::Bool(t) => TypedAstKind::Bool(t.clone()),
    //             AstKind::Ref(inner) => TypedAstKind::Ref(Box::new(TypedAstNode::from_ast(
    //                 inner,
    //                 eval_ty.clone(),
    //                 ret.clone(),
    //             ))),
    //             AstKind::Deref(inner) => TypedAstKind::Deref(Box::new(TypedAstNode::from_ast(
    //                 inner,
    //                 eval_ty.clone(),
    //                 ret.clone(),
    //             ))),
    //             AstKind::UnaryOp { op, operand } => TypedAstKind::UnaryOp {
    //                 op: op.clone(),
    //                 operand: Box::new(TypedAstNode::from_ast(
    //                     operand,
    //                     eval_ty.clone(),
    //                     ret.clone(),
    //                 )),
    //             },
    //             AstKind::BinaryOp { left, op, right } => TypedAstKind::BinaryOp {
    //                 left: Box::new(TypedAstNode::from_ast(left, eval_ty.clone(), ret.clone())),
    //                 op: op.clone(),
    //                 right: Box::new(TypedAstNode::from_ast(right, eval_ty.clone(), ret.clone())),
    //             },
    //             AstKind::VarDef { name, vartype, rhs } => TypedAstKind::VarDef {
    //                 name: name.clone(),
    //                 vartype: vartype
    //                     .as_ref()
    //                     .map(|v| Box::new(TypedAstNode::from_ast(v, eval_ty.clone(), ret.clone()))),
    //                 rhs: Box::new(TypedAstNode::from_ast(rhs, eval_ty.clone(), ret.clone())),
    //             },
    //             AstKind::Reassign { lhs, rhs } => TypedAstKind::Reassign {
    //                 lhs: Box::new(TypedAstNode::from_ast(lhs, eval_ty.clone(), ret.clone())),
    //                 rhs: Box::new(TypedAstNode::from_ast(rhs, eval_ty.clone(), ret.clone())),
    //             },
    //             AstKind::Statements(stmts) => TypedAstKind::Statements(
    //                 stmts
    //                     .iter()
    //                     .map(|c| TypedAstNode::from_ast(c, eval_ty.clone(), ret.clone()))
    //                     .collect(),
    //             ),
    //             AstKind::Items(items) => TypedAstKind::Items(
    //                 items
    //                     .iter()
    //                     .map(|c| TypedAstNode::from_ast(c, eval_ty.clone(), ret.clone()))
    //                     .collect(),
    //             ),
    //             AstKind::IfElse {
    //                 condition,
    //                 ifbody,
    //                 elsebody,
    //             } => TypedAstKind::IfElse {
    //                 condition: Box::new(TypedAstNode::from_ast(
    //                     condition,
    //                     eval_ty.clone(),
    //                     ret.clone(),
    //                 )),
    //                 ifbody: Box::new(TypedAstNode::from_ast(ifbody, eval_ty.clone(), ret.clone())),
    //                 elsebody: elsebody
    //                     .as_ref()
    //                     .map(|c| Box::new(TypedAstNode::from_ast(c, eval_ty.clone(), ret.clone()))),
    //             },
    //             AstKind::Func {
    //                 name,
    //                 params,
    //                 body,
    //                 ret: ret_node,
    //             } => TypedAstKind::Func {
    //                 name: name.clone(),
    //                 params: params
    //                     .iter()
    //                     .map(|(t, n)| {
    //                         (
    //                             t.clone(),
    //                             TypedAstNode::from_ast(n, eval_ty.clone(), ret.clone()),
    //                         )
    //                     })
    //                     .collect(),
    //                 body: Box::new(TypedAstNode::from_ast(body, eval_ty.clone(), ret.clone())),
    //                 ret: ret_node
    //                     .as_ref()
    //                     .map(|r| Box::new(TypedAstNode::from_ast(r, eval_ty.clone(), ret.clone()))),
    //             },
    //             AstKind::Loop(inner) => TypedAstKind::Loop(Box::new(TypedAstNode::from_ast(
    //                 inner,
    //                 eval_ty.clone(),
    //                 ret.clone(),
    //             ))),
    //             AstKind::Break(expr) => TypedAstKind::Break(
    //                 expr.as_ref()
    //                     .map(|e| Box::new(TypedAstNode::from_ast(e, eval_ty.clone(), ret.clone()))),
    //             ),
    //             AstKind::Return(expr) => TypedAstKind::Return(
    //                 expr.as_ref()
    //                     .map(|e| Box::new(TypedAstNode::from_ast(e, eval_ty.clone(), ret.clone()))),
    //             ),
    //             AstKind::Continue => TypedAstKind::Continue,
    //             AstKind::Disp(inner) => TypedAstKind::Disp(Box::new(TypedAstNode::from_ast(
    //                 inner,
    //                 eval_ty.clone(),
    //                 ret.clone(),
    //             ))),
    //             AstKind::FuncCall { name, args } => TypedAstKind::FuncCall {
    //                 name: name.clone(),
    //                 args: args
    //                     .iter()
    //                     .map(|c| TypedAstNode::from_ast(c, eval_ty.clone(), ret.clone()))
    //                     .collect(),
    //             },
    //             AstKind::As { lhs, rhs } => TypedAstKind::As {
    //                 lhs: Box::new(TypedAstNode::from_ast(lhs, eval_ty.clone(), ret.clone())),
    //                 rhs: rhs.clone(),
    //             },
    //             AstKind::Char(ch) => TypedAstKind::Char(ch.clone()),
    //             AstKind::Index { lhs, rhs } => TypedAstKind::Index {
    //                 lhs: Box::new(TypedAstNode::from_ast(lhs, eval_ty.clone(), ret.clone())),
    //                 rhs: Box::new(TypedAstNode::from_ast(rhs, eval_ty.clone(), ret.clone())),
    //             },
    //             AstKind::Array(items) => TypedAstKind::Array(
    //                 items
    //                     .iter()
    //                     .map(|item| TypedAstNode::from_ast(item, eval_ty.clone(), ret.clone()))
    //                     .collect(),
    //             ),
    //             AstKind::ArrayDef { size, ty } => TypedAstKind::ArrayDef {
    //                 size: size.clone(),
    //                 ty: Box::new(TypedAstNode::from_ast(ty, eval_ty, ret)),
    //             },
    //         }
    //     }

    //     TypedAstNode {
    //         kind: map_children(&ast.kind, eval_ty.clone(), ret.clone()),
    //         span: ast.span.clone(),
    //         eval_ty,
    //         ret,
    //     }
    // }
}

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
pub enum AstKind<'ip> {
    Identifier(TokenKind),
    Int(TokenKind),
    Bool(TokenKind),
    Char(TokenKind),
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
    UpdateAssign {
        lhs: Box<AstNode<'ip>>,
        op: Token<'ip>,
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
    While {
        cond: Box<AstNode<'ip>>,
        body: Box<AstNode<'ip>>,
    },
    Break(Option<Box<AstNode<'ip>>>),
    Return(Option<Box<AstNode<'ip>>>),
    Continue,
    Disp(Box<AstNode<'ip>>),
    FuncCall {
        name: Token<'ip>,
        args: Vec<AstNode<'ip>>,
    },
    As {
        lhs: Box<AstNode<'ip>>,
        rhs: Token<'ip>,
    },
    Index {
        lhs: Box<AstNode<'ip>>,
        rhs: Box<AstNode<'ip>>,
    },
    Array(Vec<AstNode<'ip>>),
    ArrayDef {
        size: Option<Token<'ip>>,
        ty: Box<AstNode<'ip>>,
    },
    String(TokenKind),
    Breakpoint,
}

impl<'ip> TypedAstKind<'ip> {
    pub fn is_leaf(&self) -> bool {
        use TypedAstKind::*;

        match self {
            Breakpoint | Identifier(_) | Int(_) | Bool(_) | Char(_) | Array(_) | String(_) => true,
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
            ArrayDef { .. } => false,
            Index { .. } => false,
            While { .. } => false,
            UpdateAssign { .. } => false,
        }
    }
}

impl<'ip> AstNode<'ip> {
    pub fn get_span(&self) -> Span<'ip> {
        self.span.clone()
    }
}
