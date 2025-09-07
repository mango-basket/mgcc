use std::collections::HashMap;

use crate::{
    error::{CompilerError, CompilerResult},
    lexer::{Token, TokenKind},
    parser::Ast,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    Unit,
}

impl Type {
    pub fn to_str(&self) -> &'static str {
        match self {
            Type::Int => "int",
            Type::Bool => "bool",
            Type::Unit => "unit",
        }
    }
}

pub type TypeEnv = HashMap<String, Type>;

// Type names and the type they mean (primitives)
fn default_type_env() -> TypeEnv {
    let mut env = HashMap::new();
    env.insert("int".to_string(), Type::Int);
    env.insert("bool".to_string(), Type::Bool);
    env.insert("unit".to_string(), Type::Unit);
    env
}

pub type VarEnv = HashMap<String, Type>;

// Identifiers and their types
fn default_var_env() -> VarEnv {
    // let mut env: VarEnv = HashMap::new();
    // env.insert("int".to_string(), Type::TypeName);
    // env.insert("bool".to_string(), Type::TypeName);
    // env

    HashMap::new()
}

pub fn check_types<'ip>(ast: Ast<'ip>) -> CompilerResult<'ip, (Ast<'ip>, VarEnv)> {
    let mut var_env: VarEnv = default_var_env();
    let type_env = default_type_env(); // immutable
    let _ = infer_type(&ast, &mut var_env, &type_env)?;
    Ok((ast, var_env))
}

fn infer_type<'ip>(
    ast: &Ast<'ip>,
    var_env: &mut VarEnv,
    type_env: &TypeEnv,
) -> CompilerResult<'ip, Type> {
    match ast {
        Ast::Int(_) => Ok(Type::Int),
        Ast::Bool(_) => Ok(Type::Bool),
        Ast::UnaryOp { op, operand } => {
            let t = infer_type(operand, var_env, type_env)?;
            match (op.kind.clone(), t) {
                (TokenKind::Minus, Type::Int)
                | (TokenKind::Plus, Type::Int)
                | (TokenKind::Xor, Type::Int) => Ok(Type::Int),
                (TokenKind::Not, Type::Bool) => Ok(Type::Bool),
                _ => Err(CompilerError::OpTypeError {
                    op: op.clone(),
                    lhs: None,
                    rhs: operand_token(operand).expect("token expected"), // always will have
                }),
            }
        }
        Ast::BinaryOp { left, op, right } => {
            let lt = infer_type(left, var_env, type_env)?;
            let rt = infer_type(right, var_env, type_env)?;

            match (op.kind.clone(), lt, rt) {
                // arithmetic
                (TokenKind::Plus, Type::Int, Type::Int)
                | (TokenKind::Minus, Type::Int, Type::Int)
                | (TokenKind::Star, Type::Int, Type::Int)
                | (TokenKind::Slash, Type::Int, Type::Int) => Ok(Type::Int),

                // equality
                (TokenKind::Eq, l, r) if l == r => Ok(Type::Bool),
                (TokenKind::Neq, l, r) if l == r => Ok(Type::Bool),

                // comparison
                (TokenKind::Gt, Type::Int, Type::Int)
                | (TokenKind::Gte, Type::Int, Type::Int)
                | (TokenKind::Lt, Type::Int, Type::Int)
                | (TokenKind::Lte, Type::Int, Type::Int) => Ok(Type::Bool),

                // logical
                (TokenKind::And, Type::Bool, Type::Bool)
                | (TokenKind::Or, Type::Bool, Type::Bool) => Ok(Type::Bool),

                // bitwise
                (TokenKind::Band, Type::Int, Type::Int)
                | (TokenKind::Bor, Type::Int, Type::Int)
                | (TokenKind::Xor, Type::Int, Type::Int) => Ok(Type::Int),

                // shifts (assuming single Bshft token)
                (TokenKind::Shl, Type::Int, Type::Int) | (TokenKind::Shr, Type::Int, Type::Int) => {
                    Ok(Type::Int)
                }

                _ => Err(CompilerError::OpTypeError {
                    op: op.clone(),
                    lhs: Some(left_token(left).expect("token expected")),
                    rhs: right_token(right).expect("token expected"),
                }),
            }
        }
        Ast::Identifier(token) => {
            if let Some(t) = var_env.get(token.slice.get_str()) {
                Ok(*t)
            } else {
                Err(CompilerError::UndefinedIdentifier {
                    ident: token.clone(),
                })
            }
        }
        Ast::Assign { name, vartype, rhs } => {
            let rhs_ty = infer_type(rhs, var_env, type_env)?;

            let final_ty = if let Some(vartype_tok) = vartype {
                match &vartype_tok.kind {
                    TokenKind::Identifier(ref s) => {
                        if let Some(t) = type_env.get(s) {
                            if *t == rhs_ty {
                                *t
                            } else {
                                return Err(CompilerError::UnexpectedType {
                                    got: rhs_ty,
                                    expected: t.to_str(),
                                    token: vartype_tok.clone(),
                                });
                            }
                        } else {
                            return Err(CompilerError::TypeError(format!(
                                "'{}' is not a known type",
                                s
                            )));
                        }
                    }
                    _ => {
                        return Err(CompilerError::UnexpectedToken {
                            got: vartype_tok.clone(),
                            expected: "identifier",
                        })
                    }
                }
            } else {
                rhs_ty
            };

            var_env.insert(name.slice.get_str().to_string(), final_ty);
            Ok(final_ty)
        }
        Ast::Reassign { name, rhs } => {
            let rhs_ty = infer_type(rhs, var_env, type_env)?;
            let var_ty =
                var_env
                    .get(name.slice.get_str())
                    .ok_or(CompilerError::UndefinedIdentifier {
                        ident: name.clone(),
                    })?;

            if *var_ty != rhs_ty {
                return Err(CompilerError::UnexpectedType {
                    got: rhs_ty,
                    expected: var_ty.to_str(),
                    token: name.clone(),
                });
            }

            Ok(*var_ty)
        }
        Ast::Statements(stmts) => {
            let mut last_ty = Type::Unit; // you'll want to define Unit later maybe
            for stmt in stmts {
                last_ty = infer_type(stmt, var_env, type_env)?;
            }
            Ok(last_ty)
        }
        Ast::IfElse {
            condition,
            ifbody,
            elsebody,
        } => {
            // type-check condition
            let cond_ty = infer_type(condition, var_env, type_env)?;
            if cond_ty != Type::Bool {
                return Err(CompilerError::UnexpectedType {
                    got: cond_ty,
                    expected: "bool",
                    token: operand_token(condition).expect("condition should have a token"),
                });
            }

            // type-check if-body
            let if_ty = infer_type(ifbody, var_env, type_env)?;

            // type-check else-body if present
            let final_ty = if let Some(else_ast) = elsebody {
                let else_ty = infer_type(else_ast, var_env, type_env)?;
                // both branches must have the same type
                if if_ty != else_ty {
                    return Err(CompilerError::UnexpectedType {
                        got: else_ty,
                        expected: if_ty.to_str(),
                        token: operand_token(else_ast).expect("else branch should have a token"),
                    });
                }
                if_ty
            } else {
                // no else, type is unit
                Type::Unit
            };

            Ok(final_ty)
        }
    }
}

fn operand_token<'ip>(ast: &Ast<'ip>) -> Option<Token<'ip>> {
    match ast {
        Ast::Identifier(t) | Ast::Int(t) | Ast::Bool(t) => Some(t.clone()),
        Ast::UnaryOp { op, .. } => Some(op.clone()),
        Ast::BinaryOp { op, .. } => Some(op.clone()),
        _ => None,
    }
}

fn left_token<'ip>(ast: &Ast<'ip>) -> Option<Token<'ip>> {
    match ast {
        Ast::Identifier(t) | Ast::Int(t) | Ast::Bool(t) => Some(t.clone()),
        Ast::UnaryOp { op, .. } => Some(op.clone()),
        Ast::BinaryOp { left, .. } => left_token(left),
        _ => None,
    }
}

fn right_token<'ip>(ast: &Ast<'ip>) -> Option<Token<'ip>> {
    match ast {
        Ast::Identifier(t) | Ast::Int(t) | Ast::Bool(t) => Some(t.clone()),
        Ast::UnaryOp { operand, .. } => operand_token(operand),
        Ast::BinaryOp { right, .. } => right_token(right),
        _ => None,
    }
}
