use std::collections::HashMap;

use crate::{
    error::{CompilerError, CompilerResult},
    lexer::{Token, TokenKind},
    parser::Ast,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    Unit,
    Ref(Box<Type>),
}

impl Type {
    pub fn to_str(&self) -> String {
        match self {
            Type::Int => "int".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Unit => "unit".to_string(),
            Type::Ref(inner) => format!("ref {}", inner.to_str()),
        }
    }

    pub fn get_size_words(&self) -> u16 {
        match self {
            Type::Int => 1,
            Type::Bool => 1,
            Type::Unit => 0,
            Type::Ref(_) => 1,
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
                    _ => {
                        let operand_token = Self::operand_token(operand).ok_or_else(|| {
                            CompilerError::Semantic(
                                "could not find token for unary operand".to_string(),
                            )
                        })?;

                        Err(CompilerError::OpTypeError {
                            op: op.clone(),
                            lhs: None,
                            rhs: operand_token,
                        })
                    }
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
                    | (TokenKind::Mod, Type::Int, Type::Int)
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

                    // shifts
                    (TokenKind::Shl, Type::Int, Type::Int)
                    | (TokenKind::Shr, Type::Int, Type::Int) => Ok(Type::Int),

                    _ => {
                        let lhs_token = Self::left_token(left).ok_or_else(|| {
                            CompilerError::Semantic(
                                "could not find token for left operand".to_string(),
                            )
                        })?;
                        let rhs_token = Self::right_token(right).ok_or_else(|| {
                            CompilerError::Semantic(
                                "could not find token for right operand".to_string(),
                            )
                        })?;

                        Err(CompilerError::OpTypeError {
                            op: op.clone(),
                            lhs: Some(lhs_token),
                            rhs: rhs_token,
                        })
                    }
                }
            }
            Ast::Identifier(token) => {
                if let Some(t) = self.var_env.get(token.slice.get_str()) {
                    Ok(t.clone())
                } else {
                    Err(CompilerError::UndefinedIdentifier(token.clone()))
                }
            }
            Ast::VarDef { name, vartype, rhs } => {
                let rhs_ty = self.infer_type(rhs)?;

                let final_ty = if let Some(vartype_ast) = vartype {
                    let annotated_ty = self.ast_to_type(vartype_ast)?;
                    if annotated_ty == rhs_ty {
                        annotated_ty
                    } else {
                        return Err(CompilerError::UnexpectedType {
                            got: rhs_ty,
                            expected: annotated_ty.to_str(),
                            slice: rhs.get_slice(),
                        });
                    }
                } else {
                    rhs_ty
                };

                self.var_env
                    .insert(name.slice.get_str().to_string(), final_ty.clone());
                Ok(final_ty)
            }
            Ast::Reassign { lhs, rhs } => {
                let rhs_ty = self.infer_type(rhs)?;
                let var_ty = self.infer_type(lhs)?;

                if var_ty != rhs_ty {
                    return Err(CompilerError::UnexpectedType {
                        got: rhs_ty,
                        expected: var_ty.to_str(),
                        slice: rhs.get_slice(),
                    });
                }

                Ok(var_ty)
            }
            Ast::Statements(stmts) => {
                let mut last_ty = Type::Unit;
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
                    let _condition_token = Self::operand_token(condition).ok_or_else(|| {
                        CompilerError::Semantic("if condition has no associated token".to_string())
                    })?;

                    return Err(CompilerError::UnexpectedType {
                        got: cond_ty,
                        expected: "bool".into(),
                        slice: condition.get_slice(),
                    });
                }

                // type-check if-body
                let if_ty = self.infer_type(ifbody)?;

                // type-check else-body if present
                let final_ty = if let Some(else_ast) = elsebody {
                    let else_ty = self.infer_type(else_ast)?;

                    // both branches must have the same type
                    if if_ty != else_ty {
                        let _else_token = Self::operand_token(else_ast).ok_or_else(|| {
                            CompilerError::Semantic(
                                "else branch has no associated token".to_string(),
                            )
                        })?;

                        return Err(CompilerError::UnexpectedType {
                            got: else_ty,
                            expected: if_ty.to_str(),
                            slice: else_ast.get_slice(),
                        });
                    }

                    if_ty
                } else {
                    // no else branch - if body must have Unit type
                    if if_ty != Type::Unit {
                        let _if_token = Self::operand_token(ifbody).ok_or_else(|| {
                            CompilerError::Semantic(
                                "if body must return unit type without else".to_string(),
                            )
                        })?;

                        return Err(CompilerError::TypeError(format!(
                                    "if expression without else branch must have unit type, but if branch has type {}. Add an else branch or change if branch to unit type.",
                                    if_ty.to_str()
                                ), ifbody.get_slice()));
                    }
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
                let break_ty_opt = self.loop_stack.pop().ok_or_else(|| {
                    CompilerError::Semantic(
                        "loop stack underflow - this indicates a compiler bug".to_string(),
                    )
                })?;

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

                // update loop frame - we know it exists because we checked above
                if let Some(top) = self.loop_stack.last_mut() {
                    match top {
                        None => *top = Some(this_ty.clone()),
                        Some(existing) => {
                            if *existing != this_ty {
                                return Err(CompilerError::TypeError(
                                    format!(
                                    "inconsistent break types in loop: expected {} but found {}",
                                    existing.to_str(),
                                    this_ty.to_str()
                                ),
                                    expr_opt.as_ref().unwrap().get_slice(),
                                ));
                            }
                        }
                    }
                } else {
                    // This should never happen because we checked in semantic_analysis.rs above
                    return Err(CompilerError::Semantic(
                        "loop stack is empty after non-empty check".to_string(),
                    ));
                }

                // always return the type of the break expression
                Ok(this_ty)
            }
            Ast::Ref(inner) => match inner.as_ref() {
                Ast::Identifier(_) | Ast::Deref(_) => {
                    let inner_ty = self.infer_type(inner)?;
                    Ok(Type::Ref(Box::new(inner_ty)))
                }
                Ast::Ref(_) => {
                    let inner_ty = self.infer_type(inner)?;
                    Ok(Type::Ref(Box::new(inner_ty)))
                }
                _ => Err(CompilerError::TypeError(
                    format!("cannot take address of this expression"),
                    inner.get_slice(),
                )),
            },
            Ast::Deref(inner) => {
                let inner_ty = self.infer_type(inner)?;
                if let Type::Ref(ty) = inner_ty {
                    Ok(*ty)
                } else {
                    Err(CompilerError::TypeError(
                        format!("cannot dereference type {}", inner_ty.to_str()),
                        inner.get_slice(),
                    ))
                }
            }
        }
    }

    fn ast_to_type<'ip>(&self, ast: &Ast<'ip>) -> CompilerResult<'ip, Type> {
        match ast {
            Ast::Identifier(name) => {
                if let Some(t) = self.type_env.get(name.slice.get_str()) {
                    Ok(t.clone())
                } else {
                    Err(CompilerError::TypeError(
                        format!("'{}' is not a known type", name.slice.get_str()),
                        name.slice.clone(),
                    ))
                }
            }
            Ast::Ref(inner) => {
                let inner_ty = self.ast_to_type(inner)?;
                Ok(Type::Ref(Box::new(inner_ty)))
            }
            _ => Err(CompilerError::Semantic(
                "invalid AST in type annotation".to_string(),
            )),
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
