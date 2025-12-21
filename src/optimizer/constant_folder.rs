use crate::error::{CompilerError, CompilerResult};
use crate::grammar::ast::{TypedAstKind, TypedAstNode};
use crate::semantic::type_check::Type;
use crate::tokenizer::token::{Token, TokenKind};

/*
What ASTKinds can apply for constant folding?
- [x] UnaryOp
- [x] BinaryOp
- [x] As

What ASTKinds are constants/literals?
- Int
- Bool
- Char
*/

pub fn fold<'ip>(ast: &'ip TypedAstNode<'ip>) -> CompilerResult<'ip, TypedAstNode> {
    match &ast.kind {
        // unary ops
        TypedAstKind::UnaryOp { op, operand } => {
            let folded_operand = fold(operand)?;
            let new_node = match (&op.kind, &folded_operand.kind) {
                (TokenKind::Minus, TypedAstKind::Int(lit)) => mk_int((!lit).wrapping_add(1), ast),
                (TokenKind::Plus, TypedAstKind::Int(_)) => folded_operand,
                (TokenKind::Not, TypedAstKind::Bool(lit)) => mk_bool(!lit, ast),
                (
                    TokenKind::Not,
                    TypedAstKind::UnaryOp {
                        op: inner_op,
                        operand: inner_operand,
                    },
                ) if inner_op.kind == TokenKind::Not && inner_operand.eval_ty == Type::Bool => {
                    (**inner_operand).clone()
                }
                (TokenKind::Bnot, TypedAstKind::Int(lit)) => mk_int(!lit, ast),
                _ => TypedAstNode::new(
                    TypedAstKind::UnaryOp {
                        op: op.clone(),
                        operand: Box::new(folded_operand),
                    },
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                ),
            };
            Ok(new_node)
        }

        // binary ops
        TypedAstKind::BinaryOp { op, left, right } => {
            let folded_left = fold(left)?;
            let folded_right = fold(right)?;

            if let Some(new) = try_short_circuit(op, &folded_left, &folded_right, ast) {
                return Ok(new);
            }
            if let Some(new) = try_constant_fold(op, &folded_left, &folded_right, ast)? {
                return Ok(new);
            }
            if let Some(new) = try_algebraic_simplify(op, &folded_left, &folded_right, ast)? {
                return Ok(new);
            }

            Ok(TypedAstNode::new(
                TypedAstKind::BinaryOp {
                    op: op.clone(),
                    left: Box::new(folded_left.clone()),
                    right: Box::new(folded_right.clone()),
                },
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }

        // type casts
        TypedAstKind::As { lhs, rhs } => {
            let folded_lhs = fold(lhs)?;
            let new_node = match (&folded_lhs.kind, rhs) {
                (TypedAstKind::Int(lit), Type::Char) => TypedAstNode::new(
                    TypedAstKind::Char(*lit as u8),
                    folded_lhs.get_span(),
                    folded_lhs.eval_ty.clone(),
                    folded_lhs.ret.clone(),
                ),
                (TypedAstKind::Bool(lit), Type::Int) => mk_int(*lit as u16, ast),
                (TypedAstKind::Char(lit), Type::Int) => mk_int(*lit as u16, ast),
                _ => TypedAstNode::new(
                    TypedAstKind::As {
                        lhs: Box::new(folded_lhs),
                        rhs: rhs.clone(),
                    },
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                ),
            };
            Ok(new_node)
        }

        // single-child nodes
        TypedAstKind::Ref(node) => {
            let folded = fold(node)?;
            Ok(TypedAstNode::new(
                TypedAstKind::Ref(Box::new(folded)),
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }
        TypedAstKind::Deref(node) => {
            let folded = fold(node)?;
            Ok(TypedAstNode::new(
                TypedAstKind::Deref(Box::new(folded)),
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }
        TypedAstKind::Disp(node) => {
            let folded = fold(node)?;
            Ok(TypedAstNode::new(
                TypedAstKind::Disp(Box::new(folded)),
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }
        TypedAstKind::Loop(node) => {
            let folded = fold(node)?;
            Ok(TypedAstNode::new(
                TypedAstKind::Loop(Box::new(folded)),
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }

        // rhs nodes
        TypedAstKind::VarDef { name, rhs } => {
            let folded_rhs = fold(rhs)?;
            Ok(TypedAstNode::new(
                TypedAstKind::VarDef {
                    name: name.clone(),
                    rhs: Box::new(folded_rhs),
                },
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }
        TypedAstKind::UpdateAssign { left, right, op } => {
            let folded_rhs = fold(right)?;
            Ok(TypedAstNode::new(
                TypedAstKind::UpdateAssign {
                    left: left.clone(),
                    right: Box::new(folded_rhs),
                    op: op.clone(),
                },
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }
        TypedAstKind::Return(Some(rhs)) => {
            let folded_rhs = fold(rhs)?;
            Ok(TypedAstNode::new(
                TypedAstKind::Return(Some(Box::new(folded_rhs))),
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }
        TypedAstKind::Break(Some(rhs)) => {
            let folded_rhs = fold(rhs)?;
            Ok(TypedAstNode::new(
                TypedAstKind::Break(Some(Box::new(folded_rhs))),
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }

        // func body
        TypedAstKind::Func { name, body } => {
            let folded_body = fold(body)?;
            Ok(TypedAstNode::new(
                TypedAstKind::Func {
                    name: name.clone(),
                    body: Box::new(folded_body),
                },
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }

        // if/else
        TypedAstKind::IfElse {
            ifbody,
            elsebody,
            condition,
        } => {
            let folded_if = fold(ifbody)?;
            let folded_else = elsebody.as_ref().map(|b| fold(b)).transpose()?;
            let folded_cond = fold(&condition)?;
            Ok(TypedAstNode::new(
                TypedAstKind::IfElse {
                    ifbody: Box::new(folded_if),
                    elsebody: folded_else.map(Box::new),
                    condition: Box::new(folded_cond),
                },
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }

        // reassignment
        TypedAstKind::Reassign { lhs, rhs } => {
            let folded_lhs = fold(lhs)?;
            let folded_rhs = fold(rhs)?;
            Ok(TypedAstNode::new(
                TypedAstKind::Reassign {
                    lhs: Box::new(folded_lhs),
                    rhs: Box::new(folded_rhs),
                },
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }

        // while
        TypedAstKind::While { cond, body } => {
            let folded_cond = fold(cond)?;
            let folded_body = fold(body)?;
            Ok(TypedAstNode::new(
                TypedAstKind::While {
                    cond: Box::new(folded_cond),
                    body: Box::new(folded_body),
                },
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }

        // index
        TypedAstKind::Index { lhs, rhs } => {
            let folded_lhs = fold(lhs)?;
            let folded_rhs = fold(rhs)?;
            Ok(TypedAstNode::new(
                TypedAstKind::Index {
                    lhs: Box::new(folded_lhs),
                    rhs: Box::new(folded_rhs),
                },
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }

        // multi-child nodes
        TypedAstKind::FuncCall { name, args } => {
            let folded_args = args
                .iter()
                .map(|a| fold(a))
                .collect::<CompilerResult<Vec<_>>>()?;
            Ok(TypedAstNode::new(
                TypedAstKind::FuncCall {
                    name: name.clone(),
                    args: folded_args,
                },
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }
        TypedAstKind::Array(args) => {
            let folded_args = args
                .iter()
                .map(|a| fold(a))
                .collect::<CompilerResult<Vec<_>>>()?;
            Ok(TypedAstNode::new(
                TypedAstKind::Array(folded_args),
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }
        TypedAstKind::Statements(args) => {
            let folded_args = args
                .iter()
                .map(|a| fold(a))
                .collect::<CompilerResult<Vec<_>>>()?;
            Ok(TypedAstNode::new(
                TypedAstKind::Statements(folded_args),
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }
        TypedAstKind::Items(args) => {
            let folded_args = args
                .iter()
                .map(|a| fold(a))
                .collect::<CompilerResult<Vec<_>>>()?;
            Ok(TypedAstNode::new(
                TypedAstKind::Items(folded_args),
                ast.get_span(),
                ast.eval_ty.clone(),
                ast.ret.clone(),
            ))
        }

        // leaf nodes
        TypedAstKind::Identifier(_)
        | TypedAstKind::Int(_)
        | TypedAstKind::Bool(_)
        | TypedAstKind::Char(_)
        | TypedAstKind::ArrayDef { .. }
        | TypedAstKind::Breakpoint
        | TypedAstKind::String(_)
        | TypedAstKind::Continue => Ok(ast.clone()),

        _ => Ok(ast.clone()),
    }
}

fn try_algebraic_simplify<'ip>(
    op: &Token<'ip>,
    left: &'ip TypedAstNode<'ip>,
    right: &'ip TypedAstNode<'ip>,
    ast: &TypedAstNode<'ip>,
) -> CompilerResult<'ip, Option<TypedAstNode<'ip>>> {
    match (
        &op.kind,
        &left.eval_ty,
        &left.kind,
        &right.eval_ty,
        &right.kind,
    ) {
        // add or subtract by 0
        (TokenKind::Plus, _, TypedAstKind::Int(0), Type::Int, _) => Ok(Some(right.clone())),
        (TokenKind::Plus | TokenKind::Minus, Type::Int, _, _, TypedAstKind::Int(0)) => {
            Ok(Some(left.clone()))
        }

        _ => Ok(None),
    }
}

fn try_constant_fold<'ip>(
    op: &Token<'ip>,
    left: &TypedAstNode<'ip>,
    right: &TypedAstNode<'ip>,
    ast: &'ip TypedAstNode<'ip>,
) -> CompilerResult<'ip, Option<TypedAstNode<'ip>>> {
    match (&op.kind, &left.kind, &right.kind) {
        // Int + Int
        (TokenKind::Plus, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_int(a.wrapping_add(*b), ast)))
        }

        // Int - Int
        (TokenKind::Minus, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_int(a.wrapping_sub(*b), ast)))
        }

        // Int * Int
        (TokenKind::Star, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_int(a.wrapping_mul(*b), ast)))
        }

        // div by 0 catch
        (TokenKind::Slash, TypedAstKind::Int(_), TypedAstKind::Int(0))
        | (TokenKind::Mod, TypedAstKind::Int(_), TypedAstKind::Int(0)) => {
            Err(CompilerError::Semantic {
                err: "cannot divide by 0".into(),
                span: ast.get_span(),
            })
        }

        // Int / Int
        (TokenKind::Slash, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_int(a.wrapping_div(*b), ast)))
        }

        // Int % Int
        (TokenKind::Mod, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_int(a.rem_euclid(*b), ast)))
        }

        // Int & Int
        (TokenKind::Band, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_int(a & b, ast)))
        }

        // Int | Int
        (TokenKind::Bor, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_int(a | b, ast)))
        }

        // Int ^ Int
        (TokenKind::Xor, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_int(a ^ b, ast)))
        }

        // Int << Int
        (TokenKind::Shl, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_int(a << b, ast)))
        }

        // Int >> Int
        (TokenKind::Slash, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_int(a >> b, ast)))
        }

        // Int == Int
        (TokenKind::Eq, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_bool(a == b, ast)))
        }

        // Bool == Bool
        (TokenKind::Eq, TypedAstKind::Bool(a), TypedAstKind::Bool(b)) => {
            Ok(Some(mk_bool(a == b, ast)))
        }

        // Char == Char
        (TokenKind::Eq, TypedAstKind::Char(a), TypedAstKind::Char(b)) => {
            Ok(Some(mk_bool(a == b, ast)))
        }

        // Int != Int
        (TokenKind::Neq, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_bool(a == b, ast)))
        }

        // Char != Char
        (TokenKind::Neq, TypedAstKind::Char(a), TypedAstKind::Char(b)) => {
            Ok(Some(mk_bool(a == b, ast)))
        }

        // Bool != Bool
        (TokenKind::Neq, TypedAstKind::Bool(a), TypedAstKind::Bool(b)) => {
            Ok(Some(mk_bool(a != b, ast)))
        }

        // Int < Int
        (TokenKind::Lt, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_bool(a < b, ast)))
        }

        // Int <= Int
        (TokenKind::Lt, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_bool(a <= b, ast)))
        }

        // Int > Int
        (TokenKind::Lt, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_bool(a > b, ast)))
        }

        // Int >= Int
        (TokenKind::Lt, TypedAstKind::Int(a), TypedAstKind::Int(b)) => {
            Ok(Some(mk_bool(a >= b, ast)))
        }

        // Bool && Bool
        (TokenKind::And, TypedAstKind::Bool(a), TypedAstKind::Bool(b)) => {
            Ok(Some(mk_bool(*a && *b, ast)))
        }

        // Bool || Bool
        (TokenKind::Or, TypedAstKind::Bool(a), TypedAstKind::Bool(b)) => {
            Ok(Some(mk_bool(*a || *b, ast)))
        }

        _ => Ok(None),
    }
}

fn try_short_circuit(
    op: &Token,
    left: &TypedAstNode,
    right: &TypedAstNode,
    ast: &TypedAstNode,
) -> Option<TypedAstNode> {
    match (&op.kind, &left.kind) {
        (TokenKind::And, TypedAstKind::Bool(false)) => Some(mk_bool(false, ast)),
        (TokenKind::And, TypedAstKind::Bool(true)) => Some(right.clone()),
        (TokenKind::Or, TypedAstKind::Bool(true)) => Some(mk_bool(true, ast)),
        (TokenKind::Or, TypedAstKind::Bool(false)) => Some(right.clone()),
        _ => None,
    }
}

fn mk_int<'ip>(val: u16, ast: &'ip TypedAstNode<'ip>) -> TypedAstNode<'ip> {
    TypedAstNode::new(
        TypedAstKind::Int(val),
        ast.get_span(),
        ast.eval_ty.clone(),
        ast.ret.clone(),
    )
}

fn mk_bool<'ip>(val: bool, ast: &'ip TypedAstNode<'ip>) -> TypedAstNode<'ip> {
    TypedAstNode::new(
        TypedAstKind::Bool(val),
        ast.get_span(),
        ast.eval_ty.clone(),
        ast.ret.clone(),
    )
}
