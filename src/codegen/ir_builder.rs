use std::collections::HashMap;

use computils::{
    error::{CompilerError, CompilerResult},
    instr::Instr,
    lexer::TokenKind,
    semantic::Type,
};

use crate::{parser::Ast, semantic::type_check::VarEnv};

type SymbolTable = HashMap<String, (u8, Type)>; // slot, type

pub struct Compiler {
    pub symbol_table: SymbolTable,
    pub last_slot: u8,
    pub var_env: VarEnv,
    pub label_counter: usize,
    pub loop_stack: Vec<(String, String)>, // (loop head, loop end)
}

impl Compiler {
    fn next_label(&mut self) -> String {
        let id = self.label_counter;
        self.label_counter += 1;
        format!("L{}", id)
    }

    fn gen_comparison(&mut self, op: &TokenKind) -> Vec<Instr> {
        let mut instrs = Vec::new();
        let lbl_true = self.next_label();
        let lbl_end = self.next_label();

        // compare left - right
        instrs.push(Instr::Cmp);

        match op {
            TokenKind::Eq => {
                instrs.push(Instr::JeqLbl(lbl_true.clone())); // equal -> true
            }
            TokenKind::Neq => {
                // not equal -> jump to true if NOT zero
                // easiest: jump if equal -> skip true
                instrs.push(Instr::JeqLbl(lbl_end.clone()));
                instrs.push(Instr::JmpLbl(lbl_true.clone()));
            }
            TokenKind::Lt => {
                instrs.push(Instr::JltLbl(lbl_true.clone())); // < -> true
            }
            TokenKind::Gt => {
                instrs.push(Instr::JgtLbl(lbl_true.clone())); // > -> true
            }
            TokenKind::Lte => {
                // <= means not (>)
                instrs.push(Instr::JgtLbl(lbl_end.clone())); // if >, skip true
                instrs.push(Instr::JmpLbl(lbl_true.clone()));
            }
            TokenKind::Gte => {
                // >= means not (<)
                instrs.push(Instr::JltLbl(lbl_end.clone())); // if <, skip true
                instrs.push(Instr::JmpLbl(lbl_true.clone()));
            }
            _ => unreachable!(),
        }

        // false branch
        instrs.push(Instr::Push(0));
        instrs.push(Instr::JmpLbl(lbl_end.clone()));

        // true branch
        instrs.push(Instr::Lbl(lbl_true));
        instrs.push(Instr::Push(1));

        // end
        instrs.push(Instr::Lbl(lbl_end));

        instrs
    }

    pub fn gen_instrs<'ip>(&mut self, ast: &'ip Ast<'ip>) -> CompilerResult<'ip, Vec<Instr>> {
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
                instrs.extend(self.gen_instrs(operand)?);
                match op.kind {
                    TokenKind::Plus => {}
                    TokenKind::Minus => instrs.push(Instr::Neg),
                    TokenKind::Bnot => instrs.push(Instr::Not),
                    TokenKind::Not => instrs.extend([Instr::Push(0), Instr::Cmp]),
                    _ => {
                        return Err(CompilerError::UnexpectedToken {
                            got: op.clone(),
                            expected: "-' or '+",
                        })
                    }
                }
            }
            Ast::BinaryOp { left, op, right } => {
                instrs.extend(self.gen_instrs(left)?);
                instrs.extend(self.gen_instrs(right)?);

                match op.kind {
                    // Arithmetic
                    TokenKind::Plus => instrs.push(Instr::Add),
                    TokenKind::Minus => instrs.push(Instr::Sub),
                    TokenKind::Star => instrs.push(Instr::Mul),
                    TokenKind::Slash => instrs.push(Instr::Div),
                    TokenKind::Mod => instrs.extend([
                        Instr::Popr(1),
                        Instr::Popr(0),
                        Instr::Pushr(0),
                        Instr::Pushr(0),
                        Instr::Pushr(1),
                        Instr::Div,
                        Instr::Pushr(1),
                        Instr::Mul,
                        Instr::Sub,
                    ]),

                    // Comparison
                    TokenKind::Eq
                    | TokenKind::Neq
                    | TokenKind::Lt
                    | TokenKind::Gt
                    | TokenKind::Lte
                    | TokenKind::Gte => instrs.extend(self.gen_comparison(&op.kind)),

                    // Logical + bitwisw
                    TokenKind::And | TokenKind::Band => instrs.push(Instr::And),
                    TokenKind::Or | TokenKind::Bor => instrs.push(Instr::Or),
                    TokenKind::Xor => instrs.push(Instr::Xor),
                    TokenKind::Shl => instrs.extend([Instr::Neg, Instr::Shft]),
                    TokenKind::Shr => instrs.push(Instr::Shft),

                    _ => {
                        return Err(CompilerError::UnexpectedToken {
                            got: op.clone(),
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
                        return Err(CompilerError::UndefinedIdentifier(token));
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
                let ty = self
                    .var_env
                    .get(name.slice.get_str())
                    .expect("typechecker ensures variables exist");

                // assign a slot for it
                self.symbol_table.insert(
                    name.slice.get_str().to_string(),
                    (self.last_slot, ty.clone()),
                );

                // generate code for rhs and store
                instrs.extend(self.gen_instrs(rhs)?);
                instrs.push(Instr::Store(self.last_slot));

                self.last_slot += 1;
            }
            Ast::Statements(asts) => {
                for ast in asts {
                    instrs.extend(self.gen_instrs(ast)?);
                }
            }
            Ast::Reassign { lhs, rhs } => match &**lhs {
                Ast::Identifier(ident_tok) => {
                    let slot = if let TokenKind::Identifier(ref ident) = ident_tok.kind {
                        if let Some((slot, _ty)) = self.symbol_table.get(ident) {
                            *slot
                        } else {
                            return Err(CompilerError::UndefinedIdentifier(ident_tok));
                        }
                    } else {
                        unreachable!()
                    };

                    instrs.extend(self.gen_instrs(rhs)?);
                    instrs.push(Instr::Store(slot));
                }
                Ast::Deref(inner) => {
                    instrs.extend(self.gen_instrs(inner)?);
                    instrs.extend(self.gen_instrs(rhs)?);
                    instrs.push(Instr::Storep);
                }
                _ => {}
            },
            Ast::IfElse {
                condition,
                ifbody,
                elsebody,
            } => {
                // generate code for condition
                instrs.extend(self.gen_instrs(condition)?);

                let lbl_else = self.next_label();
                let lbl_end = self.next_label();

                // jump to else if condition is false (0)
                instrs.extend([Instr::Push(0), Instr::Cmp, Instr::JeqLbl(lbl_else.clone())]); // assuming 0 = false, 1 = true

                // generate if-body
                instrs.extend(self.gen_instrs(ifbody)?);

                // after if-body, jump to end
                instrs.push(Instr::JmpLbl(lbl_end.clone()));

                // else-body
                instrs.push(Instr::Lbl(lbl_else));
                if let Some(else_ast) = elsebody {
                    instrs.extend(self.gen_instrs(else_ast)?);
                }

                // end label
                instrs.push(Instr::Lbl(lbl_end));
            }
            Ast::Loop(body) => {
                let head_lbl = self.next_label();
                let end_lbl = self.next_label();

                self.loop_stack.push((head_lbl.clone(), end_lbl.clone()));

                instrs.push(Instr::Lbl(head_lbl.clone()));
                instrs.extend(self.gen_instrs(body)?);
                instrs.extend([Instr::JmpLbl(head_lbl.clone()), Instr::Lbl(end_lbl.clone())]);

                self.loop_stack.pop();
            }
            Ast::Continue => instrs.push(Instr::JmpLbl(
                self.loop_stack
                    .last()
                    .ok_or(
                        CompilerError::Semantic {
                            err: "continue found outside loop (unreachable)".into(),
                            slice: ast.get_slice(),
                        }, // Shouldnt ever happen because of the semantic analyzer
                    )?
                    .0
                    .clone(),
            )),
            Ast::Break(ref opt_expr) => {
                if let Some(expr) = opt_expr {
                    instrs.extend(self.gen_instrs(expr)?);
                };

                instrs.push(Instr::JmpLbl(
                    self.loop_stack
                        .last()
                        .ok_or(
                            CompilerError::Semantic {
                                err: "break found outside loop (unreachable)".into(),
                                slice: ast.get_slice(),
                            }, // Shouldnt ever happen because of the semantic analyzer
                        )?
                        .1
                        .clone(),
                ));
            }
            Ast::Ref(inner) => {
                match **inner {
                    Ast::Identifier(ref ident_tok) => {
                        if let TokenKind::Identifier(ref name) = ident_tok.kind {
                            if let Some((slot, _ty)) = self.symbol_table.get(name) {
                                instrs.push(Instr::Pushr(5)); // push fp onto stack
                                instrs.push(Instr::Push(*slot as u16)); // push addr rel to fp
                                instrs.push(Instr::Push(2));
                                instrs.push(Instr::Mul);
                                instrs.push(Instr::Sub); // addr = fp - slot * 2
                            } else {
                                return Err(CompilerError::UndefinedIdentifier(ident_tok));
                            }
                        } else {
                            unreachable!();
                        }
                    }
                    Ast::Deref(ref inner) => instrs.extend(self.gen_instrs(inner)?),
                    _ => unreachable!(),
                }
            }
            Ast::Deref(inner) => {
                instrs.extend(self.gen_instrs(inner)?);
                instrs.push(Instr::Loadp);
            }
            Ast::Disp(printable) => {
                instrs.extend(self.gen_instrs(printable)?);
                instrs.push(Instr::Popr(0));
                instrs.push(Instr::CallLbl("print".into())) // prints r0
            }
        }

        Ok(instrs)
    }
}
