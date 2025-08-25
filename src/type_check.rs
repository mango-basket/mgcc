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
    TypeName,
}

impl Type {
    pub fn to_str(&self) -> &'static str {
        match self {
            Type::Int => "int",
            Type::Bool => "bool",
            Type::Unit => "unit",
            Type::TypeName => "typename",
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
    let mut env: VarEnv = HashMap::new();
    env.insert("int".to_string(), Type::TypeName);
    env.insert("bool".to_string(), Type::TypeName);
    env
}

pub fn check_types<'ip>(ast: Ast<'ip>) -> CompilerResult<'ip, (Ast<'ip>, TypeEnv, VarEnv)> {
    let mut var_env: VarEnv = default_var_env();
    let type_env = default_type_env(); // immutable
    let _ = infer_type(&ast, &mut var_env, &type_env)?;
    Ok((ast, type_env, var_env))
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
                (TokenKind::Minus, Type::Int) | (TokenKind::Plus, Type::Int) => Ok(Type::Int),
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
                (TokenKind::Plus, Type::Int, Type::Int)
                | (TokenKind::Minus, Type::Int, Type::Int)
                | (TokenKind::Star, Type::Int, Type::Int)
                | (TokenKind::Slash, Type::Int, Type::Int) => Ok(Type::Int),

                (TokenKind::Eq, l, r) if l == r => Ok(Type::Bool),
                (TokenKind::Neq, l, r) if l == r => Ok(Type::Bool),
                (TokenKind::Gt, Type::Int, Type::Int)
                | (TokenKind::Gte, Type::Int, Type::Int)
                | (TokenKind::Lt, Type::Int, Type::Int)
                | (TokenKind::Lte, Type::Int, Type::Int) => Ok(Type::Bool),

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
            // declared type
            let declared_ty = match &vartype.kind {
                TokenKind::Identifier(ref s) => {
                    if let Some(t) = type_env.get(s) {
                        *t
                    } else {
                        return Err(CompilerError::TypeError(format!(
                            "'{}' is not a known type",
                            s
                        )));
                    }
                }
                _ => Err(CompilerError::UnexpectedToken {
                    got: vartype.clone(),
                    expected: "identifier",
                })?,
            };

            let rhs_ty = infer_type(rhs, var_env, type_env)?;

            if declared_ty == rhs_ty {
                var_env.insert(name.slice.get_str().to_string(), declared_ty);
                Ok(declared_ty)
            } else {
                Err(CompilerError::UnexpectedType {
                    got: rhs_ty,
                    expected: declared_ty.to_str(),
                    token: vartype.clone(),
                })
            }
        }

        Ast::Statements(stmts) => {
            let mut last_ty = Type::Unit; // you'll want to define Unit later maybe
            for stmt in stmts {
                last_ty = infer_type(stmt, var_env, type_env)?;
            }
            Ok(last_ty)
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
