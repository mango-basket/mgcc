use std::collections::HashMap;

use crate::{
    codegen::ir_builder::FunctionContext,
    error::{CompilerError, CompilerResult},
    grammar::ast::{AstKind, AstNode, RetStatus, TypedAstKind, TypedAstNode},
    tokenizer::token::{Span, Token, TokenKind},
};

#[derive(Copy, Clone)]
pub enum ExprContext {
    Expr,
    Stmt,
}

#[derive(Clone, Debug)]
pub struct FnSignature {
    pub params: Vec<Type>,
    pub ret: Type,
}

#[allow(unused)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Bool,
    Unit,
    Char,
    Ref(Box<Type>),
    Array(Box<Type>, usize),
    Fn { params: Vec<Type>, ret: Box<Type> },
}

impl Type {
    pub fn to_string(&self) -> String {
        match self {
            Type::Int => "int".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Unit => "unit".to_string(),
            Type::Char => "char".to_string(),
            Type::Ref(inner) => format!("ref {}", inner.to_string()),
            Type::Fn { params, ret } => format!(
                "fn ({}) -> {}",
                params
                    .into_iter()
                    .map(|p| p.to_string())
                    .collect::<String>(),
                ret.to_string()
            ),
            Type::Array(inner, size) => format!("{}[{}]", inner.to_string(), size),
        }
    }

    pub fn get_size(&self) -> usize {
        match self {
            Type::Int => 2,
            Type::Bool => 1,
            Type::Unit => 0,
            Type::Char => 1,
            Type::Ref(_) => 2,
            Type::Array(inner, size) => inner.get_size() * size,

            // Reference
            Type::Fn { .. } => 2,
        }
    }

    pub fn get_padded_size(&self) -> usize {
        self.get_size() + (self.get_size() % 2)
    }
}

pub type TypeEnv = HashMap<String, Type>;

// Type names and the type they mean (primitives)
fn default_type_env() -> TypeEnv {
    let mut env = HashMap::new();
    env.insert("int".to_string(), Type::Int);
    env.insert("bool".to_string(), Type::Bool);
    env.insert("unit".to_string(), Type::Unit);
    env.insert("char".to_string(), Type::Char);
    env
}

pub fn check_types<'ip>(
    ast: &'ip AstNode<'ip>,
) -> CompilerResult<'ip, (TypedAstNode<'ip>, HashMap<String, FunctionContext>)> {
    let mut type_checker = TypeChecker {
        functions: HashMap::new(),
        type_env: default_type_env(),
        loop_stack: Vec::new(),
        cur_func: None,
        expr_ctx: ExprContext::Expr,
    };

    let typed = type_checker.infer_type(&ast)?;
    Ok((typed, type_checker.functions))
}

pub struct TypeChecker {
    functions: HashMap<String, FunctionContext>,
    cur_func: Option<String>,
    type_env: TypeEnv,
    loop_stack: Vec<Option<Type>>,
    expr_ctx: ExprContext,
}

impl<'ip> TypeChecker {
    pub fn add_local_to_current(&mut self, name: &str, ty: Type) -> Result<(), CompilerError<'ip>> {
        let func_name = self
            .cur_func
            .clone()
            .ok_or_else(|| CompilerError::Semantic {
                err: "no current function selected".to_string(),
                span: Default::default(),
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
                span: Default::default(),
            })?;

        if ctx.symbols.contains_key(name) {
            return Err(CompilerError::Semantic {
                err: format!(
                    "local variable '{}' already exists in function '{}'",
                    name, func_name
                ),
                span: Default::default(),
            });
        }

        let slot = ctx.fp_offset;
        ctx.symbols
            .insert(name.to_string(), (Some(slot), ty.clone()));
        // ctx.fp_offset -= ty.get_padded_size() as i8;
        ctx.fp_offset -= 2;

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
                span: Default::default(),
            })
        }
    }

    pub fn leave_function(&mut self) {
        self.cur_func = None;
    }

    pub fn declare_function(&mut self, name: &str, signature: FnSignature) -> &mut FunctionContext {
        let has_ret_slot = if signature.ret != Type::Unit { 1 } else { 0 };
        let param_size: usize = signature.params.len();

        let initial_fp_offset = 1             // old fp at fp+2
                              + 1             // return address
                              + param_size    // params (1 unit per param)
                              + has_ret_slot; // optional return slot

        let ctx = FunctionContext {
            symbols: HashMap::new(),
            fp_offset: initial_fp_offset as i8 * 2, // word size
            signature,
        };

        self.functions.insert(name.to_string(), ctx);
        self.functions.get_mut(name).unwrap()
    }

    pub fn get_function(&self, name: &str) -> Option<&FunctionContext> {
        self.functions.get(name)
    }

    fn infer_type(&mut self, ast: &'ip AstNode<'ip>) -> CompilerResult<'ip, TypedAstNode<'ip>> {
        match &ast.kind {
            AstKind::Int(tok) => Ok(TypedAstNode::new(
                TypedAstKind::Int(tok.clone()),
                ast.get_span(),
                Type::Int,
                RetStatus::Never,
            )),
            AstKind::Bool(tok) => Ok(TypedAstNode::new(
                TypedAstKind::Bool(tok.clone()),
                ast.get_span(),
                Type::Bool,
                RetStatus::Never,
            )),
            AstKind::Char(tok) => Ok(TypedAstNode::new(
                TypedAstKind::Char(tok.clone()),
                ast.get_span(),
                Type::Char,
                RetStatus::Never,
            )),
            AstKind::UnaryOp { op, operand } => self.check_unary(ast, op, operand),
            AstKind::BinaryOp { left, op, right } => self.check_binary(ast, left, op, right),
            AstKind::Identifier(_) => self.check_identifier(ast),
            AstKind::VarDef { name, vartype, rhs } => self.check_var_def(ast, name, vartype, rhs),
            AstKind::Reassign { lhs, rhs } => self.check_reassign(ast, lhs, rhs),
            AstKind::Statements(stmts) => self.check_statements(ast, stmts),
            AstKind::IfElse {
                condition,
                ifbody,
                elsebody,
            } => self.check_if(ast, condition, ifbody, elsebody),
            AstKind::Loop(body) => self.check_loop(ast, body),
            AstKind::Continue => Ok(TypedAstNode::new(
                TypedAstKind::Continue,
                ast.get_span(),
                Type::Unit,
                RetStatus::Never,
            )),
            AstKind::Break(expr_opt) => self.check_break(ast, expr_opt),
            AstKind::Ref(inner) => self.check_ref(ast, inner),
            AstKind::Deref(inner) => self.check_deref(ast, inner),
            AstKind::Disp(inner) => self.check_disp(ast, inner),
            AstKind::Items(items) => self.check_items(ast, items),
            AstKind::Func {
                name,
                params,
                body,
                ret,
            } => self.check_func(ast, name, params, body, ret),
            AstKind::Return(ret_opt) => self.check_return(ast, ret_opt),
            AstKind::FuncCall { name, args } => self.check_func_call(ast, name, args),
            AstKind::As { lhs, rhs } => self.check_as(ast, lhs, rhs),
            AstKind::Index { lhs, rhs } => self.check_index(ast, lhs, rhs),
            AstKind::Array(items) => self.check_array(ast, items),
            AstKind::ArrayDef { size, ty } => self.check_array_def(ast, size, ty),
        }
    }

    fn check_func_call(
        &mut self,
        node: &'ip AstNode<'ip>,
        name: &'ip Token<'_>,
        args: &'ip Vec<AstNode<'_>>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        let arg_types: Vec<TypedAstNode> = args
            .iter()
            .map(|a| self.infer_type(a))
            .collect::<Result<_, _>>()?;

        let func = self
            .get_function(&name.span.get_str())
            .ok_or(CompilerError::UndefinedIdentifier(name.span.clone()))?;

        if args.len() != func.signature.params.len() {
            return Err(CompilerError::Semantic {
                err: format!(
                    "function {} expects {} argument{}, but got {}",
                    name.span,
                    func.signature.params.len(),
                    if func.signature.params.len() == 1 {
                        ""
                    } else {
                        "s"
                    },
                    args.len()
                ),
                span: name.span.clone(),
            });
        }

        for (expected, got) in func.signature.params.iter().zip(arg_types.iter()) {
            if *expected != got.eval_ty {
                return Err(CompilerError::UnexpectedType {
                    got: got.eval_ty.clone(),
                    expected: expected.to_string(),
                    slice: name.span.clone(),
                });
            }
        }

        Ok(TypedAstNode::new(
            TypedAstKind::FuncCall {
                name: name.clone(),
                args: arg_types,
            },
            node.get_span(),
            func.signature.ret.clone(),
            RetStatus::Never,
        ))
    }

    fn check_return(
        &mut self,
        node: &'ip AstNode<'ip>,
        ret_opt: &'ip Option<Box<AstNode<'_>>>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        if let Some(ret_ast) = ret_opt {
            let typed = self.infer_type(ret_ast)?;
            let eval = typed.eval_ty.clone();
            Ok(TypedAstNode::new(
                TypedAstKind::Return(Some(Box::new(typed))),
                node.get_span(),
                eval.clone(),
                RetStatus::Always(eval),
            ))
        } else {
            Ok(TypedAstNode::new(
                TypedAstKind::Return(None),
                node.get_span(),
                Type::Unit,
                RetStatus::Always(Type::Unit),
            ))
        }
    }

    fn check_func(
        &mut self,
        node: &'ip AstNode<'ip>,
        name: &'ip Token<'_>,
        params: &'ip [(Token<'_>, AstNode<'_>)],
        body: &'ip AstNode<'_>,
        ret: &'ip Option<Box<AstNode<'_>>>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        // determine declared return type
        let ret_ty = if let Some(rettype_ast) = ret {
            self.ast_to_type(rettype_ast)?
        } else {
            Type::Unit
        };

        // finalize function signature
        let param_types: Vec<Type> = params
            .iter()
            .map(|(_, ast)| self.ast_to_type(ast))
            .collect::<CompilerResult<Vec<Type>>>()?;
        let params_typed: Vec<(Token<'_>, Type)> = params
            .iter()
            .zip(param_types.clone())
            .map(|((pname, _), ty)| (pname.clone(), ty))
            .collect();

        // declare function in the environment
        self.declare_function(
            name.span.get_str(),
            FnSignature {
                params: param_types.clone(),
                ret: ret_ty.clone(),
            },
        );
        self.enter_function(name.span.get_str())?;

        if ret_ty != Type::Unit {
            self.add_local_to_current("__return_addr", Type::Int)?;
        }

        // add parameters to local environment
        for (pname, ty) in params_typed.iter() {
            self.add_local_to_current(&pname.span.get_str(), ty.clone())?;
        }

        self.add_local_to_current("__return_instr_addr", Type::Int)?;
        self.add_local_to_current("__old_fp", Type::Int)?;

        // type-check body
        let body_typed = self.infer_type(body)?;
        // enforce that function body cannot be Maybe

        match &body_typed.ret {
            RetStatus::Maybe(_) => {
                return Err(CompilerError::TypeError(
                    "function body cannot have paths that may or may not return".into(),
                    body.get_span(),
                ));
            }
            RetStatus::Always(ref ty) => {
                if *ty != ret_ty {
                    return Err(CompilerError::UnexpectedType {
                        got: ty.clone(),
                        expected: ret_ty.to_string(),
                        slice: body.get_span(),
                    });
                }
            }
            RetStatus::Never => {
                if ret_ty != Type::Unit {
                    return Err(CompilerError::UnexpectedType {
                        got: Type::Unit,
                        expected: ret_ty.to_string(),
                        slice: body.get_span(),
                    });
                }
            }
        }

        self.leave_function();

        // function definition itself evaluates to Unit
        Ok(TypedAstNode::new(
            TypedAstKind::Func {
                name: name.clone(),
                params: params_typed,
                body: Box::new(body_typed),
            },
            node.get_span(),
            Type::Unit,
            RetStatus::Never,
        ))
    }

    fn check_disp(
        &mut self,
        node: &'ip AstNode<'ip>,
        inner: &'ip Box<AstNode<'ip>>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        let inner_typed = self.infer_type(inner)?;

        if inner_typed.eval_ty != Type::Char {
            return Err(CompilerError::TypeError(
                format!("cannot display {} type", inner_typed.eval_ty.to_string()),
                inner.get_span(),
            ));
        }

        Ok(TypedAstNode::new(
            TypedAstKind::Disp(Box::new(inner_typed.clone())),
            node.get_span(),
            Type::Unit,      // display itself evaluates to unit
            inner_typed.ret, // propagate the return status from the inner expression
        ))
    }

    fn check_deref(
        &mut self,
        node: &'ip AstNode<'ip>,
        inner: &'ip Box<AstNode<'ip>>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        let inner_typed = self.infer_type(inner)?;

        if let Type::Ref(ref inner_ty) = inner_typed.eval_ty {
            Ok(TypedAstNode::new(
                TypedAstKind::Deref(Box::new(inner_typed.clone())),
                node.get_span(),
                *inner_ty.clone(),
                inner_typed.ret,
            ))
        } else {
            Err(CompilerError::TypeError(
                format!(
                    "cannot dereference type {}",
                    inner_typed.eval_ty.to_string()
                ),
                inner.get_span(),
            ))
        }
    }

    fn check_ref(
        &mut self,
        node: &'ip AstNode<'ip>,
        inner: &'ip AstNode<'ip>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        let inner_typed = match inner.kind {
            AstKind::Identifier(_) | AstKind::Deref(_) | AstKind::Ref(_) => {
                self.infer_type(node)?
            }
            _ => {
                return Err(CompilerError::TypeError(
                    "cannot take address of this expression".into(),
                    node.get_span(),
                ))
            }
        };

        Ok(TypedAstNode::new(
            TypedAstKind::Ref(Box::new(inner_typed.clone())),
            node.get_span(),
            Type::Ref(Box::new(inner_typed.eval_ty)),
            inner_typed.ret,
        ))
    }

    fn check_break(
        &mut self,
        node: &'ip AstNode<'ip>,
        expr_opt: &'ip Option<Box<AstNode<'_>>>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        // type of this break (unit if no expression)
        let expr_typed = if let Some(expr) = expr_opt {
            let typed = self.infer_type(expr)?;
            Some(Box::new(typed))
        } else {
            None
        };

        let this_ty = expr_typed
            .clone()
            .map(|typed| typed.clone().eval_ty)
            .unwrap_or(Type::Unit);

        // check if we are inside a loop
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
                            expr_opt.as_ref().unwrap().get_span(),
                        ));
                    }
                }
            }
        } else {
            // break outside loop -> semantic error
            return Err(CompilerError::Semantic {
                err: "break statement used outside of a loop".to_string(),
                span: expr_opt.as_ref().map(|b| b.get_span()).unwrap_or_default(),
            });
        }

        Ok(TypedAstNode::new(
            TypedAstKind::Break(expr_typed),
            node.get_span(),
            this_ty.clone(),
            RetStatus::Never,
        ))
    }

    fn check_loop(
        &mut self,
        node: &'ip AstNode,
        body: &'ip AstNode<'_>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        self.loop_stack.push(None);

        let body_typed = self.infer_type(body)?;

        // let break_ty_opt = self.loop_stack.pop().unwrap(); // now safe

        // let ret_status = match break_ty_opt {
        //     Some(ty) => RetStatus::Always(ty.clone()),
        //     None => RetStatus::Never,
        // };

        Ok(TypedAstNode::new(
            TypedAstKind::Loop(Box::new(body_typed.clone())),
            node.get_span(),
            body_typed.eval_ty,
            body_typed.ret,
        ))
    }

    fn check_if(
        &mut self,
        node: &'ip AstNode<'ip>,
        condition: &'ip AstNode<'_>,
        ifbody: &'ip AstNode<'_>,
        elsebody: &'ip Option<Box<AstNode<'_>>>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        // type-check condition
        let cond_typed = self.infer_type(condition)?;
        if cond_typed.eval_ty != Type::Bool {
            return Err(CompilerError::UnexpectedType {
                got: cond_typed.eval_ty,
                expected: "bool".into(),
                slice: condition.get_span(),
            });
        }

        // save current context and force statement context for body type-check
        let old_ctx = self.expr_ctx;
        self.expr_ctx = ExprContext::Stmt;
        let if_typed = self.infer_type(ifbody)?;
        self.expr_ctx = old_ctx;

        let final_ty = match (&elsebody, self.expr_ctx) {
            (Some(else_ast), _) => {
                // check else-body
                let else_typed = self.infer_type(else_ast)?;

                // both branches must evaluate to the same type
                if if_typed.eval_ty != else_typed.eval_ty {
                    return Err(CompilerError::UnexpectedType {
                        got: else_typed.eval_ty,
                        expected: if_typed.eval_ty.to_string(),
                        slice: else_ast.get_span(),
                    });
                }

                let ret =
                    combine_branches(&if_typed.ret, &else_typed.ret, else_typed.span.clone())?;

                return Ok(TypedAstNode::new(
                    TypedAstKind::IfElse {
                        condition: Box::new(cond_typed),
                        ifbody: Box::new(if_typed.clone()),
                        elsebody: None,
                    },
                    node.get_span(),
                    if_typed.eval_ty,
                    ret,
                ));
            }
            (None, ExprContext::Stmt) => {
                // no else branch, in statement context → type is unit
                let ret = combine_branches(&if_typed.ret, &RetStatus::Never, ifbody.span.clone())?;
                (Type::Unit, ret)
            }
            (None, ExprContext::Expr) => {
                // no else branch in expression context → error
                return Err(CompilerError::TypeError(
                    "if expression without else branch cannot be used in expression context".into(),
                    ifbody.get_span(),
                ));
            }
        };

        Ok(TypedAstNode::new(
            TypedAstKind::IfElse {
                condition: Box::new(cond_typed),
                ifbody: Box::new(if_typed),
                elsebody: None,
            },
            node.get_span(),
            final_ty.0,
            final_ty.1,
        ))
    }

    fn check_statements(
        &mut self,
        node: &'ip AstNode<'ip>,
        stmts: &'ip Vec<AstNode<'_>>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        let old_ctx = self.expr_ctx;
        self.expr_ctx = ExprContext::Stmt;

        let mut block_ret = RetStatus::Never;
        let mut stmts_typed = Vec::new();
        for stmt in stmts {
            let typed = self.infer_type(stmt)?;
            block_ret = combine_seq(&block_ret, &typed.ret);
            stmts_typed.push(typed);
        }

        self.expr_ctx = old_ctx;

        Ok(TypedAstNode::new(
            TypedAstKind::Statements(stmts_typed),
            node.get_span(),
            Type::Unit,
            block_ret,
        ))
    }

    fn check_reassign_lhs(&mut self, node: &'ip AstNode<'ip>) -> CompilerResult<'ip, ()> {
        match &node.kind {
            AstKind::Deref(inner) => self.check_reassign_lhs(&inner),
            AstKind::Index { .. } => Ok(()),
            AstKind::Identifier(_) => Ok(()),
            _ => Err(CompilerError::Semantic {
                err: "expected ident, *deref or idx[]".into(),
                span: node.get_span(),
            }),
        }
    }

    fn check_reassign(
        &mut self,
        node: &'ip AstNode<'_>,
        lhs: &'ip AstNode<'_>,
        rhs: &'ip AstNode<'_>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        let rhs_typed = self.infer_type(rhs)?;
        let var_typed = self.infer_type(lhs)?;

        if var_typed.eval_ty != rhs_typed.eval_ty {
            return Err(CompilerError::UnexpectedType {
                got: rhs_typed.eval_ty,
                expected: var_typed.eval_ty.to_string(),
                slice: rhs.get_span(),
            });
        }

        self.check_reassign_lhs(lhs)?;

        Ok(TypedAstNode::new(
            TypedAstKind::Reassign {
                lhs: Box::new(var_typed),
                rhs: Box::new(rhs_typed.clone()),
            },
            node.get_span(),
            Type::Unit,
            rhs_typed.ret,
        ))
    }

    fn check_var_def(
        &mut self,
        node: &'ip AstNode<'_>,
        name: &'ip Token<'_>,
        vartype: &'ip Option<Box<AstNode<'_>>>,
        rhs: &'ip AstNode<'_>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        let rhs_typed = self.infer_type(rhs)?;

        let final_ty = if let Some(vartype_ast) = vartype {
            let annotated_ty = self.ast_to_type(vartype_ast)?;
            if annotated_ty == rhs_typed.eval_ty {
                annotated_ty
            } else {
                return Err(CompilerError::UnexpectedType {
                    got: rhs_typed.eval_ty,
                    expected: annotated_ty.to_string(),
                    slice: rhs.get_span(),
                });
            }
        } else {
            rhs_typed.eval_ty.clone()
        };

        self.add_local_to_current(name.span.get_str(), final_ty.clone())?;
        Ok(TypedAstNode::new(
            TypedAstKind::VarDef {
                name: name.clone(),
                rhs: Box::new(rhs_typed.clone()),
            },
            node.get_span(),
            Type::Unit,
            rhs_typed.ret,
        ))
    }

    fn check_identifier(
        &mut self,
        ident: &'ip AstNode<'_>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        if let Some(t) = self.get_local(ident.span.get_str()) {
            if let AstKind::Identifier(tok) = &ident.kind {
                Ok(TypedAstNode::new(
                    TypedAstKind::Identifier(tok.clone()),
                    ident.get_span(),
                    t.clone(),
                    RetStatus::Never,
                ))
            } else {
                unreachable!()
            }
        } else {
            Err(CompilerError::UndefinedIdentifier(ident.span.clone()))
        }
    }

    fn check_binary(
        &mut self,
        node: &'ip AstNode<'ip>,
        left: &'ip AstNode<'ip>,
        op: &'ip Token<'ip>,
        right: &'ip AstNode<'ip>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        let ltyped = self.infer_type(left)?;
        let rtyped = self.infer_type(right)?;

        let ret = combine_seq(&ltyped.ret, &rtyped.ret);

        let eval_ty = match (
            op.kind.clone(),
            ltyped.eval_ty.clone(),
            rtyped.eval_ty.clone(),
        ) {
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
            (TokenKind::Gt, a, b)
            | (TokenKind::Gte, a, b)
            | (TokenKind::Lt, a, b)
            | (TokenKind::Lte, a, b)
                if a == b && matches!(a, Type::Int | Type::Char) =>
            {
                Ok(Type::Bool)
            }

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

            _ => Err(CompilerError::OpTypeError {
                op: op.clone(),
                lhs: Some(ltyped.eval_ty.clone()),
                rhs: rtyped.eval_ty.clone(),
            }),
        }?;

        Ok(TypedAstNode::new(
            TypedAstKind::BinaryOp {
                left: Box::new(ltyped),
                op: op.clone(),
                right: Box::new(rtyped),
            },
            node.get_span(),
            eval_ty,
            ret,
        ))
    }

    fn check_unary(
        &mut self,
        node: &'ip AstNode,
        op: &'ip Token<'_>,
        operand: &'ip AstNode<'_>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        let typed = self.infer_type(operand)?;

        let (eval_ty, ret) = match (op.kind.clone(), typed.eval_ty.clone()) {
            (TokenKind::Minus, Type::Int)
            | (TokenKind::Plus, Type::Int)
            | (TokenKind::Xor, Type::Int) => (Type::Int, typed.ret.clone()),
            (TokenKind::Not, Type::Bool) => (Type::Bool, typed.ret.clone()),
            _ => {
                return Err(CompilerError::OpTypeError {
                    op: op.clone(),
                    lhs: None,
                    rhs: typed.eval_ty.clone(),
                })
            }
        };

        Ok(TypedAstNode::new(
            TypedAstKind::UnaryOp {
                op: op.clone(),
                operand: Box::new(typed),
            },
            node.get_span(),
            eval_ty,
            ret,
        ))
    }

    fn ast_to_type(&self, ast: &AstNode<'ip>) -> CompilerResult<'ip, Type> {
        match &ast.kind {
            AstKind::Identifier(_) => {
                if let Some(t) = self.type_env.get(ast.get_span().get_str()) {
                    Ok(t.clone())
                } else {
                    Err(CompilerError::TypeError(
                        format!("'{}' is not a known type", ast.get_span().get_str()),
                        ast.get_span(),
                    ))
                }
            }
            AstKind::Ref(inner) => {
                let inner_ty = self.ast_to_type(&inner)?;
                Ok(Type::Ref(Box::new(inner_ty)))
            }
            AstKind::ArrayDef { size, ty } => {
                let inner_ty = self.ast_to_type(&ty)?;
                if let TokenKind::Int(num) = size.kind {
                    Ok(Type::Array(Box::new(inner_ty), num as usize))
                } else {
                    unreachable!()
                }
            }
            other => Err(CompilerError::Semantic {
                err: format!("invalid AST {:#?} in type annotation", other),
                span: ast.get_span(),
            }),
        }
    }

    fn check_items(
        &mut self,
        node: &'ip AstNode<'ip>,
        items: &'ip [AstNode<'_>],
    ) -> CompilerResult<'ip, TypedAstNode<'ip>> {
        let mut last_ret = RetStatus::Never;
        let mut typed_items = Vec::with_capacity(items.len());

        for item in items {
            let typed_item = self.infer_type(item)?;
            last_ret = combine_seq(&last_ret, &typed_item.ret);
            typed_items.push(typed_item);
        }

        Ok(TypedAstNode::new(
            TypedAstKind::Statements(typed_items),
            node.get_span(),
            Type::Unit, // a block of items evaluates to unit
            last_ret,   // return status propagated from all items
        ))
    }

    fn check_as(
        &mut self,
        ast: &'ip AstNode<'ip>,
        lhs: &'ip AstNode<'ip>,
        rhs: &'ip Token<'ip>,
    ) -> CompilerResult<'ip, TypedAstNode<'ip>> {
        // Evalute lhs
        let lhs_ty = self.infer_type(lhs)?;

        // Assert rhs
        let rhs_ty = self
            .type_env
            .get(rhs.span.get_str())
            .ok_or(CompilerError::TypeError(
                format!("unknown type {}", rhs.span.get_str()),
                rhs.span.clone(),
            ))?;

        // match types
        let eval = match (&lhs_ty.eval_ty, rhs_ty) {
            (Type::Int, ty @ Type::Char)
            | (Type::Bool, ty @ Type::Int)
            | (Type::Char, ty @ Type::Int) => ty.clone(),
            (a, b) => {
                return Err(CompilerError::TypeError(
                    format!("cannot cast {} as {}", a.to_string(), b.to_string()),
                    ast.get_span(),
                ))
            }
        };

        Ok(TypedAstNode::new(
            TypedAstKind::As {
                lhs: Box::new(lhs_ty.clone()),
                rhs: rhs_ty.clone(),
            },
            ast.get_span(),
            eval,
            lhs_ty.ret,
        ))
    }

    fn check_index(
        &mut self,
        ast: &'ip AstNode<'ip>,
        lhs: &'ip AstNode<'ip>,
        rhs: &'ip AstNode<'ip>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        let rhs_typed = self.infer_type(rhs)?;
        if !matches!(rhs_typed.eval_ty, Type::Int) {
            return Err(CompilerError::TypeError(
                format!("cannot index with type {}", rhs_typed.eval_ty.to_string()),
                lhs.get_span(),
            ));
        }

        let lhs_typed = self.infer_type(lhs)?;
        let eval_ty = if let Type::Array(ty, _) = lhs_typed.eval_ty.clone() {
            *ty
        } else {
            return Err(CompilerError::TypeError(
                format!("cannot index type {}", lhs_typed.eval_ty.to_string()),
                lhs.get_span(),
            ));
        };

        Ok(TypedAstNode::new(
            TypedAstKind::Index {
                lhs: Box::new(lhs_typed.clone()),
                rhs: Box::new(rhs_typed.clone()),
            },
            ast.get_span(),
            eval_ty,
            combine_seq(&lhs_typed.ret, &rhs_typed.ret),
        ))
    }

    fn check_array(
        &mut self,
        ast: &'ip AstNode<'ip>,
        items: &'ip [AstNode<'_>],
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        if items.is_empty() {
            return Err(CompilerError::TypeError(
                "cannot create an empty array".into(),
                ast.get_span(),
            ));
        }

        let first_typed = self.infer_type(&items[0])?;
        let eval_ty = first_typed.eval_ty.clone();
        let mut ret = first_typed.ret.clone();

        let mut typed_items = vec![first_typed];

        for item in &items[1..] {
            let typed = self.infer_type(item)?;
            if typed.eval_ty != eval_ty {
                return Err(CompilerError::TypeError(
                    format!(
                        "type {} does not match that of previous elements, {}",
                        typed.eval_ty.to_string(),
                        eval_ty.to_string()
                    ),
                    item.get_span(),
                ));
            }
            ret = combine_seq(&ret, &typed.ret);
            typed_items.push(typed);
        }

        Ok(TypedAstNode::new(
            TypedAstKind::Array(typed_items),
            ast.get_span(),
            Type::Array(Box::new(eval_ty), items.len()),
            ret,
        ))
    }

    fn check_array_def(
        &self,
        ast: &'ip AstNode<'ip>,
        size: &'ip Token<'ip>,
        ty: &'ip AstNode<'ip>,
    ) -> Result<TypedAstNode<'ip>, CompilerError<'ip>> {
        if let TokenKind::Int(num) = size.kind {
            let elem_ty = self.ast_to_type(ty)?;

            Ok(TypedAstNode::new(
                TypedAstKind::ArrayDef {
                    ty: elem_ty.clone(),
                    size: size.clone(),
                },
                ast.get_span(),
                Type::Array(Box::new(elem_ty), num as usize),
                RetStatus::Never,
            ))
        } else {
            Err(CompilerError::TypeError(
                "array size can only be int type".into(),
                ast.get_span(),
            ))
        }
    }
}

fn combine_branches<'ip>(
    left: &RetStatus,
    right: &RetStatus,
    span: Span<'ip>,
) -> Result<RetStatus, CompilerError<'ip>> {
    use RetStatus::*;
    match (left, right) {
        // both never return
        (Never, Never) => Ok(Never),

        // both always return, must match types
        (Always(lt), Always(rt)) if lt == rt => Ok(Always(lt.clone())),
        (Always(lt), Always(rt)) => Err(CompilerError::UnexpectedType {
            got: rt.clone(),
            expected: lt.to_string(),
            slice: span,
        }),

        // both maybe return, unify types if they match
        (Maybe(lt), Maybe(rt)) if lt == rt => Ok(Maybe(lt.clone())),
        (Maybe(lt), Maybe(rt)) => Err(CompilerError::UnexpectedType {
            got: rt.clone(),
            expected: lt.to_string(),
            slice: span,
        }),

        // mix of always + never -> only some paths return
        (Always(t), Never) | (Never, Always(t)) => Ok(Maybe(t.clone())),

        // mix of always + maybe → still only maybe
        (Always(t), Maybe(u)) | (Maybe(u), Always(t)) if t == u => Ok(Maybe(t.clone())),
        (Always(t), Maybe(u)) | (Maybe(u), Always(t)) => Err(CompilerError::UnexpectedType {
            got: u.clone(),
            expected: t.to_string(),
            slice: span,
        }),

        // mix of maybe + never -> stays maybe
        (Maybe(t), Never) | (Never, Maybe(t)) => Ok(Maybe(t.clone())),
    }
}

fn combine_seq(left: &RetStatus, right: &RetStatus) -> RetStatus {
    use RetStatus::*;
    match (left, right) {
        // once you have an always-return, the rest is unreachable
        (Always(t), _) => Always(t.clone()),

        // left never returns, so outcome = right
        (Never, r) => r.clone(),

        // left maybe returns, so the overall is maybe unless right is always
        (Maybe(t), Always(u)) if t == u => Always(u.clone()),
        (Maybe(_), Always(u)) => Maybe(u.clone()), // type mismatch handled earlier
        (Maybe(t), Never) => Maybe(t.clone()),
        (Maybe(t), Maybe(u)) if t == u => Maybe(t.clone()),
        (Maybe(_), Maybe(u)) => Maybe(u.clone()), // mismatch handled earlier
    }
}
