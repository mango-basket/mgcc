use crate::error::CompilerResult;
use crate::grammar::ast::{TypedAstKind, TypedAstNode};
use crate::tokenizer::token::TokenKind;
/*
What ASTKinds can apply for constant folding?
- UnaryOp
- BinaryOp
- As

What ASTKinds are constants/literals?
- Int
- Bool
- Char
- String
*/

fn fold<'ip>(ast: &mut Box<TypedAstNode>) -> CompilerResult<'ip, ()> {
    match &mut ast.kind {
        // Unary Op
        TypedAstKind::UnaryOp { op, ref mut operand } => {
            fold(operand)?;

            *ast = match (&op.kind, &operand.kind) {
                // Negative and positive integers
                (TokenKind::Minus, TypedAstKind::Int(TokenKind::Int(lit))) => {
                    Box::new(
                        TypedAstNode::new(
                            TypedAstKind::Int(TokenKind::Int((!lit).wrapping_add(1))),
                            ast.get_span(),
                            ast.eval_ty.clone(),
                            ast.ret.clone(),
                        )
                    )
                }
                (TokenKind::Plus, TypedAstKind::Int(TokenKind::Int(lit))) => {
                    Box::new(*operand.clone())
                }

                // Logical not
                (TokenKind::Not, TypedAstKind::Bool(TokenKind::Bool(lit))) => {
                    Box::new(
                        TypedAstNode::new(
                            TypedAstKind::Bool(TokenKind::Bool(!lit)),
                            ast.get_span(),
                            ast.eval_ty.clone(),
                            ast.ret.clone(),
                        )
                    )
                }

                // Bitwise not
                (TokenKind::Bnot, TypedAstKind::Int(TokenKind::Int(lit))) => {
                    Box::new(
                        TypedAstNode::new(
                            TypedAstKind::Int(TokenKind::Int(!lit)),
                            ast.get_span(),
                            ast.eval_ty.clone(),
                            ast.ret.clone(),
                        )
                    )
                }

                (_, _) => return Ok(()),
            };
        }

        TypedAstKind::BinaryOp { op, ref mut left, ref mut right} => {
            fold(left)?;
            fold(right)?;

            *ast = match (&op.kind, &left.kind, &right.kind) {
                // Int + Int
                // Int - Int
                // Int * Int
                // Int / Int
                // Int % Int

                // Lit is Int | Bool | Char
                // I can rely on typechecker to make sure they are compatible

                // Lit == Lit
                // Lit != Lit
                // Lit < Lit
                // Lit <= Lit
                // Lit > Lit
                // Lit >= Lit

                // Bool && Bool
                // Bool || Bool
                // Int & Int
                // Int | Int
                // Int ^ Int
                // Int << Int
                // Int >> Int

                (_, _, _) => return Ok(()),
            };
        }

        _ => return Ok(()),
    }

    Ok(())
}