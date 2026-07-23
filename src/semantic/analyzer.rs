use std::collections::HashMap;

use crate::{
    codegen::ir_builder::FunctionContext,
    error::{CompilerError, CompilerResult},
    grammar::ast::{TypedAstKind, TypedAstNode},
    semantic::type_check::Type,
    tokenizer::token::Span,
};

pub struct SemanticChecker<'a> {
    loop_depth: usize,
    funcs: &'a HashMap<String, FunctionContext>,
}

pub fn check_semantics<'ip>(
    ast: &'ip TypedAstNode<'ip>,
    funcs: &HashMap<String, FunctionContext>,
    lib: bool,
) -> CompilerResult<'ip, ()> {
    let mut checker = SemanticChecker::new(funcs);
    // checker.check_main()?;
    checker.check(ast)?;

    let mut seen_module = false;
    validate_lib_mode(ast, lib, &mut seen_module)?;

    if lib && !seen_module {
        return Err(CompilerError::Semantic {
            err: "--lib compilation requires a module declaration at the top of the file"
                .to_string(),
            span: Span::new(0, 0, ""),
        });
    }

    Ok(())
}

fn validate_lib_mode<'ip>(
    ast: &'ip TypedAstNode<'ip>,
    lib: bool,
    seen_module: &mut bool,
) -> CompilerResult<'ip, ()> {
    match &ast.kind {
        TypedAstKind::Module(name) => {
            if !lib {
                return Err(CompilerError::Semantic {
                    err: "use of module/export requires the --lib flag".to_string(),
                    span: name.span.clone(),
                });
            }
            if *seen_module {
                return Err(CompilerError::Semantic {
                    err: "duplicate module declaration".to_string(),
                    span: name.span.clone(),
                });
            }
            *seen_module = true;
        }
        TypedAstKind::Func { is_export, name, .. } => {
            if *is_export && !lib {
                return Err(CompilerError::Semantic {
                    err: "use of module/export requires the --lib flag".to_string(),
                    span: name.span.clone(),
                });
            }
        }
        TypedAstKind::Items(items) | TypedAstKind::Statements(items) => {
            for item in items {
                validate_lib_mode(item, lib, seen_module)?;
            }
        }
        TypedAstKind::IfElse {
            ifbody,
            elsebody,
            ..
        } => {
            validate_lib_mode(ifbody, lib, seen_module)?;
            if let Some(else_ast) = elsebody {
                validate_lib_mode(else_ast, lib, seen_module)?;
            }
        }
        TypedAstKind::Loop(body) | TypedAstKind::While { body, .. } => {
            validate_lib_mode(body, lib, seen_module)?;
        }
        _ => {}
    }
    Ok(())
}

impl<'a> SemanticChecker<'a> {
    pub fn new(funcs: &'a HashMap<String, FunctionContext>) -> Self {
        Self {
            loop_depth: 0,
            funcs,
        }
    }

    pub fn check_main<'ip>(&self) -> CompilerResult<'ip, ()> {
        if !self.funcs.contains_key("main") {
            return Err(CompilerError::Semantic {
                err: "main function not found".to_string(),
                span: Span::new(0, 0, ""),
            });
        }

        let func_sig = self.funcs["main"].signature.clone();
        if func_sig.params.len() != 0 {
            return Err(CompilerError::Semantic {
                err: format!("main expects 0 parameters, found {}", func_sig.params.len()),
                span: Span::new(0, 0, ""),
            });
        }

        if func_sig.ret != Type::Unit {
            return Err(CompilerError::Semantic {
                err: "main function must return unit type".to_string(),
                span: Span::new(0, 0, ""),
            });
        }

        Ok(())
    }

    pub fn check<'ip>(&mut self, ast: &'ip TypedAstNode<'ip>) -> CompilerResult<'ip, ()> {
        match &ast.kind {
            TypedAstKind::Break(_) | TypedAstKind::Continue => {
                if self.loop_depth == 0 {
                    return Err(CompilerError::Semantic {
                        err: "break/continue outside of loop".to_string(),
                        span: ast.get_span(),
                    });
                }
                Ok(())
            }
            TypedAstKind::Loop(body) => {
                self.loop_depth += 1;
                self.check(&*body)?;
                self.loop_depth -= 1;
                Ok(())
            }
            TypedAstKind::While { cond, body } => {
                self.loop_depth += 1;
                self.check(&*body)?;
                self.check(&*cond)?;
                self.loop_depth -= 1;
                Ok(())
            }
            TypedAstKind::Statements(stmts) | TypedAstKind::Items(stmts) => {
                for stmt in stmts {
                    self.check(&stmt)?;
                }
                Ok(())
            }
            TypedAstKind::IfElse {
                condition: _,
                ifbody,
                elsebody,
            } => {
                self.check(&ifbody)?;
                if let Some(else_ast) = elsebody {
                    self.check(&else_ast)?;
                }
                Ok(())
            }
            TypedAstKind::UnaryOp { operand, .. } => self.check(&operand),
            TypedAstKind::BinaryOp { left, right, .. }
            | TypedAstKind::UpdateAssign { left, right, .. } => {
                self.check(&left)?;
                self.check(&right)
            }
            TypedAstKind::VarDef { rhs, .. } => self.check(&rhs),
            TypedAstKind::Reassign { lhs, rhs } => {
                self.check(&lhs)?;
                self.check(&rhs)?;

                match lhs.kind {
                    TypedAstKind::Identifier(_)
                    | TypedAstKind::Deref(_)
                    | TypedAstKind::Index { .. } => Ok(()),
                    _ => Err(CompilerError::Semantic {
                        err: "invalid left-hand side in assignment".to_string(),
                        span: lhs.get_span(),
                    }),
                }
            }
            TypedAstKind::Ref(inner) => match &inner.kind {
                TypedAstKind::Identifier(_) | TypedAstKind::Deref(_) => Ok(()),
                TypedAstKind::Ref(inner2) => self.check(&inner2),
                _ => Err(CompilerError::Semantic {
                    err: "cannot take reference of a temporary expression".to_string(),
                    span: inner.get_span(),
                }),
            },
            TypedAstKind::Deref(_) => Ok(()),
            TypedAstKind::Disp(_) => Ok(()),
            TypedAstKind::Int(_)
            | TypedAstKind::Bool(_)
            | TypedAstKind::Char(_)
            | TypedAstKind::String(_)
            | TypedAstKind::Identifier(_) => Ok(()),
            TypedAstKind::Func { body, .. } => {
                // check function body recursively
                self.check(&body)
            }
            TypedAstKind::Return(_ast) => Ok(()),
            TypedAstKind::FuncCall { .. } => Ok(()),
            TypedAstKind::As { .. } => Ok(()),
            TypedAstKind::Index { .. } => Ok(()),
            TypedAstKind::Array(_) => Ok(()),
            TypedAstKind::ArrayDef { .. } => Ok(()),
            TypedAstKind::Breakpoint => Ok(()),
            TypedAstKind::Module(_) => Ok(()),
        }
    }
}
