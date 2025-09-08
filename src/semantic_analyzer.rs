use crate::error::{CompilerError, CompilerResult};
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
                    return Err(CompilerError::Semantic(
                        "break/continue outside of loop".to_string(),
                    ));
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

            Ast::VarDef { rhs, .. } | Ast::Reassign { rhs, .. } => self.check(rhs),

            Ast::Int(_) | Ast::Bool(_) | Ast::Identifier(_) => Ok(()),
        }
    }
}
