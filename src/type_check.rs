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
    let mut type_checker = TypeChecker {
        var_env: default_var_env(),
        type_env: default_type_env(),
        loop_stack: Vec::new(),
    };

    let _ = type_checker.infer_type(&ast)?;
    Ok((ast, type_checker.var_env))
}

pub struct TypeChecker {
    var_env: VarEnv,
    type_env: TypeEnv,
    loop_stack: Vec<Option<Type>>,
}

impl TypeChecker {
    fn infer_type<'ip>(&mut self, ast: &Ast<'ip>) -> CompilerResult<'ip, Type> {
        match ast {
            Ast::Int(_) => Ok(Type::Int),
            Ast::Bool(_) => Ok(Type::Bool),
            Ast::UnaryOp { op, operand } => {
                let t = self.infer_type(operand)?;
                match (op.kind.clone(), t) {
                    (TokenKind::Minus, Type::Int)
                    | (TokenKind::Plus, Type::Int)
                    | (TokenKind::Xor, Type::Int) => Ok(Type::Int),
                    (TokenKind::Not, Type::Bool) => Ok(Type::Bool),
                    _ => Err(CompilerError::OpTypeError {
                        op: op.clone(),
                        lhs: None,
                        rhs: Self::operand_token(operand).expect("token expected"), // always will have
                    }),
                }
            }
            Ast::BinaryOp { left, op, right } => {
                let lt = self.infer_type(left)?;
                let rt = self.infer_type(right)?;

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
                    (TokenKind::Shl, Type::Int, Type::Int)
                    | (TokenKind::Shr, Type::Int, Type::Int) => Ok(Type::Int),

                    _ => Err(CompilerError::OpTypeError {
                        op: op.clone(),
                        lhs: Some(Self::left_token(left).expect("token expected")),
                        rhs: Self::right_token(right).expect("token expected"),
                    }),
                }
            }
            Ast::Identifier(token) => {
                if let Some(t) = self.var_env.get(token.slice.get_str()) {
                    Ok(*t)
                } else {
                    Err(CompilerError::UndefinedIdentifier {
                        ident: token.clone(),
                    })
                }
            }
            Ast::VarDef { name, vartype, rhs } => {
                let rhs_ty = self.infer_type(rhs)?;

                let final_ty = if let Some(vartype_tok) = vartype {
                    match &vartype_tok.kind {
                        TokenKind::Identifier(ref s) => {
                            if let Some(t) = self.type_env.get(s) {
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

                self.var_env
                    .insert(name.slice.get_str().to_string(), final_ty);
                Ok(final_ty)
            }
            Ast::Reassign { name, rhs } => {
                let rhs_ty = self.infer_type(rhs)?;
                let var_ty = self.var_env.get(name.slice.get_str()).ok_or(
                    CompilerError::UndefinedIdentifier {
                        ident: name.clone(),
                    },
                )?;

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
                    last_ty = self.infer_type(stmt)?;
                }
                Ok(last_ty)
            }
            Ast::IfElse {
                condition,
                ifbody,
                elsebody,
            } => {
                // type-check condition
                let cond_ty = self.infer_type(condition)?;
                if cond_ty != Type::Bool {
                    return Err(CompilerError::UnexpectedType {
                        got: cond_ty,
                        expected: "bool",
                        token: Self::operand_token(condition)
                            .expect("condition should have a token"),
                    });
                }

                // type-check if-body
                let if_ty = self.infer_type(ifbody)?;

                // type-check else-body if present
                let final_ty = if let Some(else_ast) = elsebody {
                    let else_ty = self.infer_type(else_ast)?;

                    // both branches must have the same type
                    if if_ty != else_ty {
                        return Err(CompilerError::UnexpectedType {
                            got: else_ty,
                            expected: if_ty.to_str(),
                            token: Self::operand_token(else_ast)
                                .expect("else branch should have a token"),
                        });
                    }

                    if_ty
                } else {
                    // no else, type is unit
                    Type::Unit
                };

                Ok(final_ty)
            }
            Ast::Loop(body) => {
                // push a new frame for this loop
                self.loop_stack.push(None);

                // type-check the body
                let _ = self.infer_type(body)?;

                // pop the frame and get the break type
                let break_ty_opt = self.loop_stack.pop().expect("loop stack push/pop mismatch");

                // loop type is either the break type or unit if no breaks
                if let Some(ty) = break_ty_opt {
                    Ok(ty)
                } else {
                    Ok(Type::Unit)
                }
            }
            Ast::Continue => Ok(Type::Unit),
            Ast::Break(expr_opt) => {
                // type of this break (unit if no expression)
                let this_ty = if let Some(expr) = expr_opt {
                    self.infer_type(expr)?
                } else {
                    Type::Unit
                };

                // update loop frame if inside a loop
                if let Some(top) = self.loop_stack.last_mut() {
                    match top {
                        None => *top = Some(this_ty),
                        Some(existing) => {
                            if *existing != this_ty {
                                return Err(CompilerError::TypeError(format!(
                                    "inconsistent break types in loop: {:?} vs {:?}",
                                    existing, this_ty
                                )));
                            }
                        }
                    }
                }

                // always return the type of the break expression
                Ok(this_ty)
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
            Ast::BinaryOp { left, .. } => Self::left_token(left),
            _ => None,
        }
    }

    fn right_token<'ip>(ast: &Ast<'ip>) -> Option<Token<'ip>> {
        match ast {
            Ast::Identifier(t) | Ast::Int(t) | Ast::Bool(t) => Some(t.clone()),
            Ast::UnaryOp { operand, .. } => Self::operand_token(operand),
            Ast::BinaryOp { right, .. } => Self::right_token(right),
            _ => None,
        }
    }
}
