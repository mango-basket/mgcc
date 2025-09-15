use std::{collections::HashMap, fmt::format};

use crate::{
    codegen::ir_builder::FunctionContext,
    error::{CompilerError, CompilerResult},
    grammar::ast::Ast,
    tokenizer::token::{Token, TokenKind},
};
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    Unit,
    Ref(Box<Type>),
    Fn { params: Vec<Type>, ret: Box<Type> },
}

impl Type {
    pub fn to_string(&self) -> String {
        match self {
            Type::Int => "int".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Unit => "unit".to_string(),
            Type::Ref(inner) => format!("ref {}", inner.to_string()),
            Type::Fn { params, ret } => format!(
                "fn ({}) -> {}",
                params
                    .into_iter()
                    .map(|p| p.to_string())
                    .collect::<String>(),
                ret.to_string()
            ),
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

pub fn check_types<'ip>(
    ast: &'ip Ast<'ip>,
) -> CompilerResult<'ip, HashMap<String, FunctionContext>> {
    let mut type_checker = TypeChecker {
        functions: HashMap::new(),
        type_env: default_type_env(),
        loop_stack: Vec::new(),
        cur_func: None,
    };

    let _ = type_checker.infer_type(&ast)?;
    Ok(type_checker.functions)
}

pub struct TypeChecker {
    functions: HashMap<String, FunctionContext>,
    cur_func: Option<String>,
    type_env: TypeEnv,
    loop_stack: Vec<Option<Type>>,
}

impl<'ip> TypeChecker {
    pub fn add_local_to_current(&mut self, name: &str, ty: Type) -> Result<(), CompilerError<'ip>> {
        let func_name = self
            .cur_func
            .clone()
            .ok_or_else(|| CompilerError::Semantic {
                err: "no current function selected".to_string(),
                slice: Default::default(),
            })?;
        self.add_local(&func_name, name, ty)
    }

    pub fn add_local(
        &mut self,
        func_name: &str,
        name: &str,
        ty: Type,
    ) -> Result<(), CompilerError<'ip>> {
        let ctx = self
            .functions
            .get_mut(func_name)
            .ok_or_else(|| CompilerError::Semantic {
                err: format!("function '{}' not found", func_name),
                slice: Default::default(),
            })?;

        if ctx.symbols.contains_key(name) {
            return Err(CompilerError::Semantic {
                err: format!(
                    "local variable '{}' already exists in function '{}'",
                    name, func_name
                ),
                slice: Default::default(),
            });
        }

        let slot = ctx.next_slot;
        ctx.symbols.insert(name.to_string(), (Some(slot), ty));
        ctx.next_slot += 1;

        Ok(())
    }

    pub fn get_local(&self, name: &str) -> Option<&Type> {
        let func_name = self.cur_func.as_ref()?;
        self.functions
            .get(func_name)?
            .symbols
            .get(name)
            .map(|(_, ty)| ty)
    }

    pub fn enter_function(&mut self, name: &str) -> Result<(), CompilerError<'ip>> {
        if self.functions.contains_key(name) {
            self.cur_func = Some(name.to_string());
            Ok(())
        } else {
            Err(CompilerError::Semantic {
                err: format!("function '{}' does not exist", name),
                slice: Default::default(),
            })
        }
    }

    pub fn leave_function(&mut self) {
        self.cur_func = None;
    }

    pub fn declare_function(&mut self, name: &str, ret_type: Type) -> &mut FunctionContext {
        let ctx = FunctionContext {
            symbols: HashMap::new(),
            next_slot: 0,
            ret_type,
        };
        self.functions.insert(name.to_string(), ctx);
        self.functions.get_mut(name).unwrap()
    }

    pub fn get_function(&self, name: &str) -> Option<&FunctionContext> {
        self.functions.get(name)
    }

    pub fn get_function_mut(&mut self, name: &str) -> Option<&mut FunctionContext> {
        self.functions.get_mut(name)
    }

    pub fn has_function(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }

    fn infer_type(&mut self, ast: &'ip Ast<'ip>) -> CompilerResult<'ip, Type> {
        match ast {
            Ast::Int(_) => Ok(Type::Int),
            Ast::Bool(_) => Ok(Type::Bool),
            Ast::UnaryOp { op, operand } => self.check_unary(op, operand),
            Ast::BinaryOp { left, op, right } => self.check_binary(left, op, right),
            Ast::Identifier(token) => self.check_identifier(token),
            Ast::VarDef { name, vartype, rhs } => self.check_var_def(name, vartype, rhs),
            Ast::Reassign { lhs, rhs } => self.check_reassign(lhs, rhs),
            Ast::Statements(stmts) => self.check_statements(stmts),
            Ast::IfElse {
                condition,
                ifbody,
                elsebody,
            } => self.check_if(condition, ifbody, elsebody),
            Ast::Loop(body) => self.check_loop(body),
            Ast::Continue => Ok(Type::Unit),
            Ast::Break(expr_opt) => self.check_break(expr_opt),
            Ast::Ref(inner) => self.check_ref(inner),
            Ast::Deref(inner) => self.check_deref(inner),
            Ast::Disp(inner) => self.check_disp(inner),
            Ast::Items(_) => Ok(Type::Unit), // I dont think i need to type check this. def regretting this decision sometime in the future
            Ast::Func {
                name,
                params,
                body,
                ret,
            } => self.check_func(name, params, body, ret),
            Ast::Return(ast) => todo!(),
        }
    }

    fn check_func(
        &mut self,
        name: &'ip Token<'_>,
        params: &'ip [(Token<'_>, Ast<'_>)],
        body: &'ip Ast<'_>,
        ret: &'ip Option<Box<Ast<'_>>>,
    ) -> Result<Type, CompilerError<'ip>> {
        let name_str = name.slice.get_str();

        // check for redefs
        if self.get_function(&name_str).is_some() {
            return Err(CompilerError::Semantic {
                err: format!("function {} already defined once before", name_str),
                slice: name.slice.clone(),
            });
        }

        self.enter_function(&name_str);

        let mut params_ty = Vec::new();

        for (_pname, ast) in params {
            let param_ty = self.ast_to_type(ast)?;
            params_ty.push(param_ty);
        }

        let mut body_ty = None;
        if let Ast::Statements(stmts) = body {
            for stmt in stmts {
                match stmt {
                    Ast::Return(_) => {
                        let ret_ty = self.infer_type(stmt)?;
                        if body_ty.is_none() {
                            body_ty = Some(self.infer_type(stmt)?);
                        } else if body_ty.clone().unwrap() != ret_ty {
                            return Err(CompilerError::UnexpectedType {
                                got: ret_ty,
                                expected: body_ty.unwrap().to_string(),
                                slice: stmt.get_slice(),
                            });
                        }
                    }
                    _ => {
                        self.infer_type(stmt)?;
                    }
                }
            }
        }

        let body_ty = body_ty.unwrap_or(Type::Unit);

        let ret_ty = if let Some(rettype_ast) = ret {
            self.ast_to_type(rettype_ast)?
        } else {
            Type::Unit
        };

        if body_ty != ret_ty {
            return Err(CompilerError::UnexpectedType {
                got: body_ty,
                expected: ret_ty.to_string(),
                slice: body.get_slice(),
            });
        }

        self.declare_function(name_str, ret_ty);

        self.leave_function();
        Ok(Type::Unit)
    }

    fn check_disp(&mut self, inner: &'ip Box<Ast<'ip>>) -> Result<Type, CompilerError<'ip>> {
        let inner_ty = self.infer_type(inner)?;
        if inner_ty == Type::Unit {
            return Err(CompilerError::TypeError(
                "cannot display unit type".into(),
                inner.get_slice(),
            ));
        }

        Ok(Type::Unit)
    }

    fn check_deref(&mut self, inner: &'ip Box<Ast<'ip>>) -> Result<Type, CompilerError<'ip>> {
        let inner_ty = self.infer_type(inner)?;
        if let Type::Ref(ty) = inner_ty {
            Ok(*ty)
        } else {
            Err(CompilerError::TypeError(
                format!("cannot dereference type {}", inner_ty.to_string()),
                inner.get_slice(),
            ))
        }
    }

    fn check_ref(&mut self, inner: &'ip Box<Ast<'ip>>) -> Result<Type, CompilerError<'ip>> {
        match inner.as_ref() {
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
        }
    }

    fn check_break(
        &mut self,
        expr_opt: &'ip Option<Box<Ast<'_>>>,
    ) -> Result<Type, CompilerError<'ip>> {
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
                                existing.to_string(),
                                this_ty.to_string()
                            ),
                            expr_opt.as_ref().unwrap().get_slice(),
                        ));
                    }
                }
            }
        } else {
            // This should never happen because we checked in semantic_analysis.rs above
            return Err(CompilerError::Semantic {
                err: "loop stack is empty after non-empty check".to_string(),
                slice: expr_opt.as_ref().unwrap().get_slice(),
            });
        }

        // always return the type of the break expression
        Ok(this_ty)
    }

    fn check_loop(&mut self, body: &'ip Box<Ast<'_>>) -> Result<Type, CompilerError<'ip>> {
        // push a new frame for this loop
        self.loop_stack.push(None);

        // type-check the body
        let _ = self.infer_type(body)?;

        // pop the frame and get the break type
        let break_ty_opt = self
            .loop_stack
            .pop()
            .ok_or_else(|| CompilerError::Semantic {
                err: "loop stack underflow - this indicates a compiler bug".to_string(),
                slice: body.get_slice(),
            })?;

        // loop type is either the break type or unit if no breaks
        if let Some(ty) = break_ty_opt {
            Ok(ty)
        } else {
            Ok(Type::Unit)
        }
    }

    fn check_if(
        &mut self,
        condition: &'ip Box<Ast<'_>>,
        ifbody: &'ip Box<Ast<'_>>,
        elsebody: &'ip Option<Box<Ast<'_>>>,
    ) -> Result<Type, CompilerError<'ip>> {
        // type-check condition
        let cond_ty = self.infer_type(condition)?;
        if cond_ty != Type::Bool {
            Self::operand_token(condition).ok_or_else(|| CompilerError::Semantic {
                err: "if condition has no associated token".to_string(),
                slice: condition.get_slice(),
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
                let _else_token =
                    Self::operand_token(else_ast).ok_or_else(|| CompilerError::Semantic {
                        err: "else branch has no associated token".to_string(),
                        slice: else_ast.get_slice(),
                    })?;

                return Err(CompilerError::UnexpectedType {
                    got: else_ty,
                    expected: if_ty.to_string(),
                    slice: else_ast.get_slice(),
                });
            }

            if_ty
        } else {
            // no else branch - if body must have Unit type
            if if_ty != Type::Unit {
                let _if_token =
                    Self::operand_token(ifbody).ok_or_else(|| CompilerError::Semantic {
                        err: "if body must return unit type without else".to_string(),
                        slice: ifbody.get_slice(),
                    })?;

                return Err(CompilerError::TypeError(format!(
                                            "if expression without else branch must have unit type, but if branch has type {}. Add an else branch or change if branch to unit type.",
                                            if_ty.to_string()
                                        ), ifbody.get_slice()));
            }
            Type::Unit
        };

        Ok(final_ty)
    }

    fn check_statements(&mut self, stmts: &'ip Vec<Ast<'_>>) -> Result<Type, CompilerError<'ip>> {
        let mut last_ty = Type::Unit;
        for stmt in stmts {
            last_ty = self.infer_type(stmt)?;
        }
        Ok(last_ty)
    }

    fn check_reassign(
        &mut self,
        lhs: &'ip Box<Ast<'_>>,
        rhs: &'ip Box<Ast<'_>>,
    ) -> Result<Type, CompilerError<'ip>> {
        let rhs_ty = self.infer_type(rhs)?;
        let var_ty = self.infer_type(lhs)?;

        if var_ty != rhs_ty {
            return Err(CompilerError::UnexpectedType {
                got: rhs_ty,
                expected: var_ty.to_string(),
                slice: rhs.get_slice(),
            });
        }

        Ok(var_ty)
    }

    fn check_var_def(
        &mut self,
        name: &Token<'_>,
        vartype: &'ip Option<Box<Ast<'_>>>,
        rhs: &'ip Box<Ast<'_>>,
    ) -> Result<Type, CompilerError<'ip>> {
        let rhs_ty = self.infer_type(rhs)?;

        let final_ty = if let Some(vartype_ast) = vartype {
            let annotated_ty = self.ast_to_type(vartype_ast)?;
            if annotated_ty == rhs_ty {
                annotated_ty
            } else {
                return Err(CompilerError::UnexpectedType {
                    got: rhs_ty,
                    expected: annotated_ty.to_string(),
                    slice: rhs.get_slice(),
                });
            }
        } else {
            rhs_ty
        };

        self.add_local_to_current(name.slice.get_str(), final_ty.clone());
        Ok(final_ty)
    }

    fn check_identifier(&mut self, token: &'ip Token<'_>) -> Result<Type, CompilerError<'ip>> {
        if let Some(t) = self.get_local(token.slice.get_str()) {
            Ok(t.clone())
        } else {
            Err(CompilerError::UndefinedIdentifier(token))
        }
    }

    fn check_binary(
        &mut self,
        left: &'ip Box<Ast<'_>>,
        op: &'ip Token<'_>,
        right: &'ip Box<Ast<'_>>,
    ) -> Result<Type, CompilerError<'ip>> {
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
            (TokenKind::And, Type::Bool, Type::Bool) | (TokenKind::Or, Type::Bool, Type::Bool) => {
                Ok(Type::Bool)
            }

            // bitwise
            (TokenKind::Band, Type::Int, Type::Int)
            | (TokenKind::Bor, Type::Int, Type::Int)
            | (TokenKind::Xor, Type::Int, Type::Int) => Ok(Type::Int),

            // shifts
            (TokenKind::Shl, Type::Int, Type::Int) | (TokenKind::Shr, Type::Int, Type::Int) => {
                Ok(Type::Int)
            }

            _ => {
                let lhs_token = Self::left_token(left).ok_or_else(|| CompilerError::Semantic {
                    err: "could not find token for left operand".to_string(),
                    slice: left.get_slice(),
                })?;
                let rhs_token =
                    Self::right_token(right).ok_or_else(|| CompilerError::Semantic {
                        err: "could not find token for right operand".to_string(),
                        slice: right.get_slice(),
                    })?;

                Err(CompilerError::OpTypeError {
                    op: op.clone(),
                    lhs: Some(lhs_token),
                    rhs: rhs_token,
                })
            }
        }
    }

    fn check_unary(
        &mut self,
        op: &'ip Token<'_>,
        operand: &'ip Box<Ast<'_>>,
    ) -> Result<Type, CompilerError<'ip>> {
        let t = self.infer_type(operand)?;
        match (op.kind.clone(), t) {
            (TokenKind::Minus, Type::Int)
            | (TokenKind::Plus, Type::Int)
            | (TokenKind::Xor, Type::Int) => Ok(Type::Int),
            (TokenKind::Not, Type::Bool) => Ok(Type::Bool),
            _ => {
                let operand_token =
                    Self::operand_token(operand).ok_or_else(|| CompilerError::Semantic {
                        err: "could not find token for unary operand".to_string(),
                        slice: operand.get_slice(),
                    })?;

                Err(CompilerError::OpTypeError {
                    op: op.clone(),
                    lhs: None,
                    rhs: operand_token,
                })
            }
        }
    }

    fn ast_to_type(&self, ast: &Ast<'ip>) -> CompilerResult<'ip, Type> {
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
            _ => Err(CompilerError::Semantic {
                err: "invalid AST in type annotation".to_string(),
                slice: ast.get_slice(),
            }),
        }
    }

    fn operand_token(ast: &Ast<'ip>) -> Option<Token<'ip>> {
        match ast {
            Ast::Identifier(t) | Ast::Int(t) | Ast::Bool(t) => Some(t.clone()),
            Ast::UnaryOp { op, .. } => Some(op.clone()),
            Ast::BinaryOp { op, .. } => Some(op.clone()),
            _ => None,
        }
    }

    fn left_token(ast: &Ast<'ip>) -> Option<Token<'ip>> {
        match ast {
            Ast::Identifier(t) | Ast::Int(t) | Ast::Bool(t) => Some(t.clone()),
            Ast::UnaryOp { op, .. } => Some(op.clone()),
            Ast::BinaryOp { left, .. } => Self::left_token(left),
            _ => None,
        }
    }

    fn right_token(ast: &Ast<'ip>) -> Option<Token<'ip>> {
        match ast {
            Ast::Identifier(t) | Ast::Int(t) | Ast::Bool(t) => Some(t.clone()),
            Ast::UnaryOp { operand, .. } => Self::operand_token(operand),
            Ast::BinaryOp { right, .. } => Self::right_token(right),
            _ => None,
        }
    }
}
