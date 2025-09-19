use std::collections::HashMap;

use crate::{
    codegen::ir_builder::FunctionContext,
    error::{CompilerError, CompilerResult},
    grammar::ast::Ast,
    semantic::type_check::Type,
    tokenizer::token::Slice,
};

pub struct SemanticChecker<'a> {
    loop_depth: usize,
    funcs: &'a HashMap<String, FunctionContext>,
}

pub fn check_semantics<'ip>(
    ast: &Ast<'ip>,
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
                slice: Slice::new(0, 0, ""),
            });
        }

        let func_sig = self.funcs["main"].signature.clone();
        if func_sig.params.len() != 0 {
            return Err(CompilerError::Semantic {
                err: format!("main expects 0 parameters, found {}", func_sig.params.len()),
                slice: Slice::new(0, 0, ""),
            });
        }

        if func_sig.ret != Type::Unit {
            return Err(CompilerError::Semantic {
                err: "main function must return unit type".to_string(),
                slice: Slice::new(0, 0, ""),
            });
        }

        Ok(())
    }

    pub fn check<'ip>(&mut self, ast: &Ast<'ip>) -> CompilerResult<'ip, ()> {
        match ast {
            Ast::Break(_) | Ast::Continue => {
                if self.loop_depth == 0 {
                    return Err(CompilerError::Semantic {
                        err: "break/continue outside of loop".to_string(),
                        slice: ast.get_slice(),
                    });
                }
                Ok(())
            }
            Ast::Loop(body) => {
                self.loop_depth += 1;
                self.check(body)?;
                self.loop_depth -= 1;
                Ok(())
            }
            Ast::Statements(stmts) => {
                for stmt in stmts {
                    self.check(stmt)?;
                }
                Ok(())
            }
            Ast::IfElse {
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
            Ast::UnaryOp { operand, .. } => self.check(operand),
            Ast::BinaryOp { left, right, .. } => {
                self.check(left)?;
                self.check(right)
            }
            Ast::VarDef { rhs, .. } => self.check(rhs),
            Ast::Reassign { lhs, rhs } => {
                self.check(lhs)?;
                self.check(rhs)?;

                // If we have a deref we can be guaranteed that its a valid deref
                match lhs.as_ref() {
                    Ast::Identifier(_) | Ast::Deref(_) => Ok(()),
                    _ => Err(CompilerError::Semantic {
                        err: "invalid left-hand side in assignment".to_string(),
                        slice: lhs.get_slice(),
                    }),
                }
            }
            Ast::Ref(inner) => match inner.as_ref() {
                Ast::Identifier(_) | Ast::Deref(_) => Ok(()),
                Ast::Ref(inner2) => Ok(self.check(inner2)?),
                _ => Err(CompilerError::Semantic {
                    err: "cannot take reference of a temporary expression".to_string(),
                    slice: inner.get_slice(),
                }),
            },
            Ast::Deref(_) => Ok(()),
            Ast::Disp(_) => Ok(()),
            Ast::Int(_) | Ast::Bool(_) | Ast::Identifier(_) => Ok(()),
            Ast::Items(_asts) => Ok(()),
            Ast::Func {
                name: _,
                params: _,
                body: _,
                ret: _,
            } => Ok(()),
            Ast::Return(_ast) => Ok(()),
            Ast::FuncCall { .. } => Ok(()),
        }
    }
}
