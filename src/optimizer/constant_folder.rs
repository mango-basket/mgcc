use crate::error::{CompilerError, CompilerResult};
use crate::grammar::ast::{TypedAstKind, TypedAstNode};
use crate::semantic::type_check::Type;
use crate::tokenizer::token::TokenKind;

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

fn fold<'ip>(ast: &mut Box<TypedAstNode<'ip>>) -> CompilerResult<'ip, ()> {
    match &mut ast.kind {
        // Unary Op
        TypedAstKind::UnaryOp {
            op,
            ref mut operand,
        } => {
            fold(operand)?;

            *ast = match (&op.kind, &operand.kind) {
                // Negative and positive integers
                (TokenKind::Minus, TypedAstKind::Int(TokenKind::Int(lit))) => {
                    Box::new(TypedAstNode::new(
                        TypedAstKind::Int(TokenKind::Int((!lit).wrapping_add(1))),
                        ast.get_span(),
                        ast.eval_ty.clone(),
                        ast.ret.clone(),
                    ))
                }
                (TokenKind::Plus, TypedAstKind::Int(TokenKind::Int(lit))) => {
                    Box::new(*operand.clone())
                }

                // Logical not
                (TokenKind::Not, TypedAstKind::Bool(TokenKind::Bool(lit))) => {
                    Box::new(TypedAstNode::new(
                        TypedAstKind::Bool(TokenKind::Bool(!lit)),
                        ast.get_span(),
                        ast.eval_ty.clone(),
                        ast.ret.clone(),
                    ))
                }

                // Bitwise not
                (TokenKind::Bnot, TypedAstKind::Int(TokenKind::Int(lit))) => {
                    Box::new(TypedAstNode::new(
                        TypedAstKind::Int(TokenKind::Int(!lit)),
                        ast.get_span(),
                        ast.eval_ty.clone(),
                        ast.ret.clone(),
                    ))
                }

                (_, _) => return Ok(()),
            };
        }

        TypedAstKind::BinaryOp {
            op,
            ref mut left,
            ref mut right,
        } => {
            fold(left)?;
            fold(right)?;

            *ast = match (&op.kind, &left.kind, &right.kind) {
                // Int + Int
                (
                    TokenKind::Plus,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Int(TokenKind::Int(lit1.wrapping_add(*lit2))),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int - Int
                (
                    TokenKind::Minus,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Int(TokenKind::Int(lit1.wrapping_sub(*lit2))),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int * Int
                (
                    TokenKind::Star,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Int(TokenKind::Int(lit1.wrapping_mul(*lit2))),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int / Int
                // check for zeroes
                (
                    TokenKind::Slash,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => {
                    if *lit2 == 0 {
                        return Err(CompilerError::Semantic {
                            err: format!("cannot divide by 0"),
                            span: ast.get_span(),
                        });
                    }

                    Box::new(TypedAstNode::new(
                        TypedAstKind::Int(TokenKind::Int(lit1.wrapping_div(*lit2))),
                        ast.get_span(),
                        ast.eval_ty.clone(),
                        ast.ret.clone(),
                    ))
                }

                // Int % Int
                (
                    TokenKind::Mod,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => {
                    if *lit2 == 0 {
                        return Err(CompilerError::Semantic {
                            err: format!("cannot divide by 0"),
                            span: ast.get_span(),
                        });
                    }

                    Box::new(TypedAstNode::new(
                        TypedAstKind::Int(TokenKind::Int(lit1.rem_euclid(*lit2))),
                        ast.get_span(),
                        ast.eval_ty.clone(),
                        ast.ret.clone(),
                    ))
                }

                // Lit is Int | Bool | Char
                // I can rely on typechecker to make sure they are compatible

                // Lit == Lit
                (
                    TokenKind::Eq,
                    TypedAstKind::Int(kind1)
                    | TypedAstKind::Bool(kind1)
                    | TypedAstKind::Char(kind1),
                    TypedAstKind::Int(kind2)
                    | TypedAstKind::Bool(kind2)
                    | TypedAstKind::Char(kind2),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Bool(TokenKind::Bool(kind1 == kind2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Lit != Lit
                (
                    TokenKind::Neq,
                    TypedAstKind::Int(kind1)
                    | TypedAstKind::Bool(kind1)
                    | TypedAstKind::Char(kind1),
                    TypedAstKind::Int(kind2)
                    | TypedAstKind::Bool(kind2)
                    | TypedAstKind::Char(kind2),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Bool(TokenKind::Bool(kind1 != kind2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int < Int
                (
                    TokenKind::Lt,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Bool(TokenKind::Bool(lit1 < lit2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int <= Int
                (
                    TokenKind::Lte,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Bool(TokenKind::Bool(lit1 <= lit2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int > Int
                (
                    TokenKind::Gt,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Bool(TokenKind::Bool(lit1 >= lit2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int >= Int
                (
                    TokenKind::Gte,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Bool(TokenKind::Bool(lit1 >= lit2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Bool && Bool
                (
                    TokenKind::And,
                    TypedAstKind::Bool(TokenKind::Bool(lit1)),
                    TypedAstKind::Bool(TokenKind::Bool(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Bool(TokenKind::Bool(*lit1 && *lit2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Bool || Bool
                (
                    TokenKind::And,
                    TypedAstKind::Bool(TokenKind::Bool(lit1)),
                    TypedAstKind::Bool(TokenKind::Bool(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Bool(TokenKind::Bool(*lit1 || *lit2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int & Int
                (
                    TokenKind::Band,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Int(TokenKind::Int(lit1 & lit2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int | Int
                (
                    TokenKind::Bor,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Int(TokenKind::Int(lit1 | lit2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int ^ Int
                (
                    TokenKind::Xor,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Int(TokenKind::Int(lit1 ^ lit2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int << Int
                (
                    TokenKind::Shl,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Int(TokenKind::Int(lit1 << lit2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                // Int >> Int
                (
                    TokenKind::Shr,
                    TypedAstKind::Int(TokenKind::Int(lit1)),
                    TypedAstKind::Int(TokenKind::Int(lit2)),
                ) => Box::new(TypedAstNode::new(
                    TypedAstKind::Int(TokenKind::Int(lit1 >> lit2)),
                    ast.get_span(),
                    ast.eval_ty.clone(),
                    ast.ret.clone(),
                )),

                (_, _, _) => return Ok(()),
            };
        }

        TypedAstKind::As { ref mut lhs, rhs } => {
            fold(lhs)?;

            *ast = match (&lhs.kind, rhs) {
                // Int as Char
                (TypedAstKind::Int(TokenKind::Int(lit)), Type::Char) => {
                    Box::new(TypedAstNode::new(
                        TypedAstKind::Char(TokenKind::Char(*lit as u8)),
                        ast.get_span(),
                        ast.eval_ty.clone(),
                        ast.ret.clone(),
                    ))
                }

                // Bool as Int
                (TypedAstKind::Bool(TokenKind::Bool(lit)), Type::Int) => {
                    Box::new(TypedAstNode::new(
                        TypedAstKind::Int(TokenKind::Int(*lit as u16)),
                        ast.get_span(),
                        ast.eval_ty.clone(),
                        ast.ret.clone(),
                    ))
                }

                // Char as Int
                (TypedAstKind::Char(TokenKind::Char(lit)), Type::Int) => {
                    Box::new(TypedAstNode::new(
                        TypedAstKind::Int(TokenKind::Int(*lit as u16)),
                        ast.get_span(),
                        ast.eval_ty.clone(),
                        ast.ret.clone(),
                    ))
                }

                (_, _) => return Ok(()),
            }
        }

        _ => return Ok(()),
    }

    Ok(())
}
