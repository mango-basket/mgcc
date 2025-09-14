use computils::error::{CompilerError, CompilerResult};

use crate::parser::Ast;

pub struct SemanticChecker {
    loop_depth: usize,
}

pub fn check_semantics<'ip>(ast: &Ast<'ip>) -> CompilerResult<'ip, ()> {
    let mut checker = SemanticChecker::new();
    checker.check(ast)
}

impl SemanticChecker {
    pub fn new() -> Self {
        Self { loop_depth: 0 }
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

            // check rhs, check lhs to be a valid deref or variable name
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
        }
    }
}
