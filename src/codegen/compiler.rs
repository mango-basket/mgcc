use std::collections::HashMap;

use crate::{
    codegen::Instr,
    error::{CompilerError, CompilerResult},
    lexer::TokenKind,
    parser::Ast,
    type_check::{Type, VarEnv},
};

type SymbolTable = HashMap<String, (u8, Type)>;

pub struct Compiler {
    pub symbol_table: SymbolTable,
    pub last_slot: u8,
    pub var_env: VarEnv,
    pub label_counter: usize,
    pub loop_stack: Vec<(usize, usize)>, // (loop head, loop end)
}

impl Compiler {
    fn next_label(&mut self) -> usize {
        let id = self.label_counter;
        self.label_counter += 1;
        id
    }

    fn gen_comparison(&mut self, op: TokenKind) -> Vec<Instr> {
        let mut instrs = Vec::new();
        let lbl_true = self.next_label();
        let lbl_end = self.next_label();

        // compare left - right
        instrs.push(Instr::Icmp);

        match op {
            TokenKind::Eq => {
                instrs.push(Instr::JeqLbl(lbl_true)); // equal -> true
            }
            TokenKind::Neq => {
                // not equal -> jump to true if NOT zero
                // easiest: jump if equal -> skip true
                instrs.push(Instr::JeqLbl(lbl_end));
                instrs.push(Instr::JmpLbl(lbl_true));
            }
            TokenKind::Lt => {
                instrs.push(Instr::JltLbl(lbl_true)); // < -> true
            }
            TokenKind::Gt => {
                instrs.push(Instr::JgtLbl(lbl_true)); // > -> true
            }
            TokenKind::Lte => {
                // <= means not (>)
                instrs.push(Instr::JgtLbl(lbl_end)); // if >, skip true
                instrs.push(Instr::JmpLbl(lbl_true));
            }
            TokenKind::Gte => {
                // >= means not (<)
                instrs.push(Instr::JltLbl(lbl_end)); // if <, skip true
                instrs.push(Instr::JmpLbl(lbl_true));
            }
            _ => unreachable!(),
        }

        // false branch
        instrs.push(Instr::Push(0));
        instrs.push(Instr::JmpLbl(lbl_end));

        // true branch
        instrs.push(Instr::Lbl(lbl_true));
        instrs.push(Instr::Push(1));

        // end
        instrs.push(Instr::Lbl(lbl_end));

        instrs
    }

    pub fn gen_instrs<'ip>(&mut self, ast: Ast<'ip>) -> CompilerResult<'ip, Vec<Instr>> {
        let mut instrs = Vec::new();

        match ast {
            Ast::Int(tok) => {
                if let TokenKind::Int(num) = tok.kind {
                    instrs.push(Instr::Push(num))
                } else {
                    unreachable!()
                }
            }
            Ast::UnaryOp { op, operand } => {
                instrs.extend(self.gen_instrs(*operand)?);
                match op.kind {
                    TokenKind::Plus => {}
                    TokenKind::Minus => instrs.push(Instr::Neg),
                    TokenKind::Bnot => instrs.push(Instr::Not),
                    TokenKind::Not => instrs.extend([Instr::Push(0), Instr::Icmp]),
                    _ => {
                        return Err(CompilerError::UnexpectedToken {
                            got: op,
                            expected: "-' or '+",
                        })
                    }
                }
            }
            Ast::BinaryOp { left, op, right } => {
                instrs.extend(self.gen_instrs(*left)?);
                instrs.extend(self.gen_instrs(*right)?);

                match op.kind {
                    // Arithmetic
                    TokenKind::Plus => instrs.push(Instr::Iadd),
                    TokenKind::Minus => instrs.push(Instr::Isub),
                    TokenKind::Star => instrs.push(Instr::Imul),
                    TokenKind::Slash => instrs.push(Instr::Idiv),

                    // Comparison
                    TokenKind::Eq
                    | TokenKind::Neq
                    | TokenKind::Lt
                    | TokenKind::Gt
                    | TokenKind::Lte
                    | TokenKind::Gte => instrs.extend(self.gen_comparison(op.kind)),

                    // Logical + bitwisw
                    TokenKind::And | TokenKind::Band => instrs.push(Instr::And),
                    TokenKind::Or | TokenKind::Bor => instrs.push(Instr::Or),
                    TokenKind::Xor => instrs.push(Instr::Xor),
                    TokenKind::Shl => instrs.extend([Instr::Neg, Instr::Shft]),
                    TokenKind::Shr => instrs.push(Instr::Shft),

                    _ => {
                        return Err(CompilerError::UnexpectedToken {
                            got: op,
                            expected: "+', '-', '*' or '/",
                        })
                    }
                }
            }
            Ast::Identifier(token) => {
                if let TokenKind::Identifier(ref name) = token.kind {
                    if let Some((slot, _ty)) = self.symbol_table.get(name) {
                        instrs.push(Instr::Load(*slot));
                    } else {
                        return Err(CompilerError::UndefinedIdentifier { ident: token });
                    }
                } else {
                    unreachable!();
                }
            }
            Ast::Bool(token) => {
                if let TokenKind::Bool(bool) = token.kind {
                    instrs.push(Instr::Push(bool as u16));
                } else {
                    unreachable!()
                }
            }
            Ast::VarDef {
                name,
                vartype: _,
                rhs,
            } => {
                // look up type from var_env (guaranteed by typechecker)
                let ty = *self
                    .var_env
                    .get(name.slice.get_str())
                    .expect("typechecker ensures variables exist");

                // assign a slot for it
                self.symbol_table
                    .insert(name.slice.get_str().to_string(), (self.last_slot, ty));

                // generate code for rhs and store
                instrs.extend(self.gen_instrs(*rhs)?);
                instrs.push(Instr::Store(self.last_slot));

                self.last_slot += 1;
            }
            Ast::Statements(asts) => {
                for ast in asts {
                    instrs.extend(self.gen_instrs(*ast)?);
                }
            }
            Ast::Reassign { name, rhs } => {
                let slot = if let TokenKind::Identifier(ref ident) = name.kind {
                    if let Some((slot, _ty)) = self.symbol_table.get(ident) {
                        *slot
                    } else {
                        return Err(CompilerError::UndefinedIdentifier { ident: name });
                    }
                } else {
                    unreachable!()
                };

                instrs.extend(self.gen_instrs(*rhs)?);
                instrs.push(Instr::Store(slot));
            }
            Ast::IfElse {
                condition,
                ifbody,
                elsebody,
            } => {
                // generate code for condition
                instrs.extend(self.gen_instrs(*condition)?);

                let lbl_else = self.next_label();
                let lbl_end = self.next_label();

                // jump to else if condition is false (0)
                instrs.extend([Instr::Push(0), Instr::Icmp, Instr::JeqLbl(lbl_else)]); // assuming 0 = false, 1 = true

                // generate if-body
                instrs.extend(self.gen_instrs(*ifbody)?);

                // after if-body, jump to end
                instrs.push(Instr::JmpLbl(lbl_end));

                // else-body
                instrs.push(Instr::Lbl(lbl_else));
                if let Some(else_ast) = elsebody {
                    instrs.extend(self.gen_instrs(*else_ast)?);
                }

                // end label
                instrs.push(Instr::Lbl(lbl_end));
            }
            Ast::Loop(body) => {
                let head_lbl = self.next_label();
                let end_lbl = self.next_label();

                self.loop_stack.push((head_lbl, end_lbl));

                instrs.push(Instr::Lbl(head_lbl));
                instrs.extend(self.gen_instrs(*body)?);
                instrs.extend([Instr::JmpLbl(head_lbl), Instr::Lbl(end_lbl)]);

                self.loop_stack.pop();
            }
            Ast::Continue => instrs.push(Instr::JmpLbl(
                self.loop_stack
                    .last()
                    .ok_or(
                        CompilerError::Semantic("continue found outside loop (unreachable)".into()), // Shouldnt ever happen because of the semantic analyzer
                    )?
                    .0,
            )),
            Ast::Break(opt_expr) => {
                if let Some(expr) = opt_expr {
                    instrs.extend(self.gen_instrs(*expr)?);
                };

                instrs.push(Instr::JmpLbl(
                    self.loop_stack
                        .last()
                        .ok_or(
                            CompilerError::Semantic(
                                "break found outside loop (unreachable)".into(),
                            ), // Shouldnt ever happen because of the semantic analyzer
                        )?
                        .1,
                ));
            }
        }

        Ok(instrs)
    }
}
