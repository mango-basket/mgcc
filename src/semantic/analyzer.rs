use std::collections::HashMap;

use crate::{
    codegen::ir_builder::FunctionContext,
    error::{CompilerError, CompilerResult},
    grammar::ast::{AstKind, AstNode},
    semantic::type_check::Type,
    tokenizer::token::Span,
};

pub struct SemanticChecker<'a> {
    loop_depth: usize,
    funcs: &'a HashMap<String, FunctionContext>,
}

pub fn check_semantics<'ip>(
    ast: &AstNode<'ip>,
    funcs: &HashMap<String, FunctionContext>,
) -> CompilerResult<'ip, ()> {
    let mut checker = SemanticChecker::new(funcs);
    checker.check_main()?;
    checker.check(ast)
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
                slice: Span::new(0, 0, ""),
            });
        }

        let func_sig = self.funcs["main"].signature.clone();
        if func_sig.params.len() != 0 {
            return Err(CompilerError::Semantic {
                err: format!("main expects 0 parameters, found {}", func_sig.params.len()),
                slice: Span::new(0, 0, ""),
            });
        }

        if func_sig.ret != Type::Unit {
            return Err(CompilerError::Semantic {
                err: "main function must return unit type".to_string(),
                slice: Span::new(0, 0, ""),
            });
        }

        Ok(())
    }

    pub fn check<'ip>(&mut self, ast: &AstNode<'ip>) -> CompilerResult<'ip, ()> {
        match &ast.kind {
            AstKind::Break(_) | AstKind::Continue => {
                if self.loop_depth == 0 {
                    return Err(CompilerError::Semantic {
                        err: "break/continue outside of loop".to_string(),
                        slice: ast.get_slice(),
                    });
                }
                Ok(())
            }
            AstKind::Loop(body) => {
                self.loop_depth += 1;
                self.check(body)?;
                self.loop_depth -= 1;
                Ok(())
            }
            AstKind::Statements(stmts) => {
                for stmt in stmts {
                    self.check(stmt)?;
                }
                Ok(())
            }
            AstKind::IfElse {
                condition: _,
                ifbody,
                elsebody,
            } => {
                self.check(ifbody)?;
                if let Some(else_ast) = elsebody {
                    self.check(else_ast)?;
                }
                Ok(())
            }
            AstKind::UnaryOp { operand, .. } => self.check(operand),
            AstKind::BinaryOp { left, right, .. } => {
                self.check(left)?;
                self.check(right)
            }
            AstKind::VarDef { rhs, .. } => self.check(rhs),
            AstKind::Reassign { lhs, rhs } => {
                self.check(lhs)?;
                self.check(rhs)?;

                // If we have a deref we can be guaranteed that its a valid deref
                match lhs.kind {
                    AstKind::Identifier(_) | AstKind::Deref(_) => Ok(()),
                    _ => Err(CompilerError::Semantic {
                        err: "invalid left-hand side in assignment".to_string(),
                        slice: lhs.get_slice(),
                    }),
                }
            }
            AstKind::Ref(inner) => match &inner.kind {
                AstKind::Identifier(_) | AstKind::Deref(_) => Ok(()),
                AstKind::Ref(inner2) => Ok(self.check(&inner2)?),
                _ => Err(CompilerError::Semantic {
                    err: "cannot take reference of a temporary expression".to_string(),
                    slice: inner.get_slice(),
                }),
            },
            AstKind::Deref(_) => Ok(()),
            AstKind::Disp(_) => Ok(()),
            AstKind::Int(_) | AstKind::Bool(_) | AstKind::Identifier(_) => Ok(()),
            AstKind::Items(_asts) => Ok(()),
            AstKind::Func {
                name: _,
                params: _,
                body: _,
                ret: _,
            } => Ok(()),
            AstKind::Return(_ast) => Ok(()),
            AstKind::FuncCall { .. } => Ok(()),
        }
    }
}
