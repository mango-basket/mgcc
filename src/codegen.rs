use std::collections::HashMap;

use crate::{
    error::{CompilerError, CompilerResult},
    lexer::TokenKind,
    parser::Ast,
    type_check::{Type, TypeEnv, VarEnv},
};

pub enum Instr {
    Push(u32),
    Load(u8),
    Store(u8),
    Icmp,
    Jmp(i8),
    Jlt(i8),
    Jgt(i8),
    Jeq(i8),
    Iadd,
    Isub,
    Imul,
    Idiv,
    Neg,
    Not,
    Halt,
}

type SymbolTable = HashMap<String, (u8, Type)>;

struct Compiler {
    symbol_table: SymbolTable,
    last_slot: u8,
    type_env: TypeEnv,
    var_env: VarEnv,
}

pub fn gen_instrs<'ip>(
    ast: Ast<'ip>,
    type_env: TypeEnv,
    var_env: VarEnv,
) -> CompilerResult<'ip, Vec<Instr>> {
    let mut compiler = Compiler {
        symbol_table: HashMap::new(),
        last_slot: 0,
        type_env,
        var_env,
    };

    let mut ret = compiler.gen_instrs(ast)?;
    ret.push(Instr::Halt);
    Ok(ret)
}

impl Compiler {
    fn gen_instrs<'ip>(&mut self, ast: Ast<'ip>) -> CompilerResult<'ip, Vec<Instr>> {
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
                    TokenKind::Not => instrs.push(Instr::Not),
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
                    TokenKind::Eq => instrs.extend([
                        Instr::Icmp,
                        Instr::Jeq(2),
                        Instr::Push(0),
                        Instr::Jmp(1),
                        Instr::Push(1),
                    ]),
                    TokenKind::Neq => instrs.extend([
                        Instr::Icmp,
                        Instr::Jeq(2),
                        Instr::Push(1),
                        Instr::Jmp(1),
                        Instr::Push(0),
                    ]),
                    TokenKind::Gt => instrs.extend([
                        Instr::Icmp,
                        Instr::Jgt(2),
                        Instr::Push(0),
                        Instr::Jmp(1),
                        Instr::Push(1),
                    ]),
                    TokenKind::Lt => instrs.extend([
                        Instr::Icmp,
                        Instr::Jlt(2),
                        Instr::Push(0),
                        Instr::Jmp(1),
                        Instr::Push(1),
                    ]),
                    TokenKind::Gte => instrs.extend([
                        Instr::Icmp,
                        Instr::Jeq(3),
                        Instr::Jgt(2),
                        Instr::Push(0),
                        Instr::Jmp(1),
                        Instr::Push(1),
                    ]),
                    TokenKind::Lte => instrs.extend([
                        Instr::Icmp,
                        Instr::Jlt(3),
                        Instr::Jeq(2),
                        Instr::Push(0),
                        Instr::Jmp(1),
                        Instr::Push(1),
                    ]),
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
                    if let Some(addr) = self.symbol_table.get(name) {
                        instrs.push(Instr::Load(addr.0));
                    } else {
                        return Err(CompilerError::UndefinedIdentifier { ident: token });
                    }
                } else {
                    unreachable!();
                }
            }
            Ast::Bool(token) => {
                if let TokenKind::Bool(bool) = token.kind {
                    instrs.push(Instr::Push(bool as u32));
                } else {
                    unreachable!()
                }
            }
            Ast::Assign { name, vartype, rhs } => {
                // Assign a slot for it
                let vartype = if let TokenKind::Identifier(name) = vartype.kind {
                    match self.type_env.get(&name) {
                        Some(t) => t,
                        None => match self.var_env.get(&name) {
                            Some(t) => t,
                            None => unreachable!(),
                        },
                    }
                } else {
                    unreachable!()
                };
                self.symbol_table
                    .insert(name.slice.get_str().to_string(), (self.last_slot, *vartype));

                // Write the instructions for it
                instrs.extend(self.gen_instrs(*rhs)?);
                instrs.push(Instr::Store(self.last_slot));

                self.last_slot += 1;
            }
            Ast::Statements(asts) => {
                for ast in asts {
                    instrs.extend(self.gen_instrs(*ast)?);
                }
            }
        }

        Ok(instrs)
    }
}

pub fn gen_code(instrs: Vec<Instr>) -> String {
    let mut code = String::new();

    for instr in instrs {
        code.push_str(&match instr {
            Instr::Push(num) => format!("PUSH {}", num),
            Instr::Load(addr) => format!("LOAD {}", addr),
            Instr::Store(addr) => format!("STOR {}", addr),
            Instr::Halt => "HALT".into(),
            Instr::Iadd => "IADD".into(),
            Instr::Isub => "ISUB".into(),
            Instr::Imul => "IMUL".into(),
            Instr::Idiv => "IDIV".into(),
            Instr::Neg => "NEG".into(),
            Instr::Not => "NOT".into(),
            Instr::Icmp => "ICMP".into(),
            Instr::Jmp(ofst) => format!("JMP {}", ofst),
            Instr::Jlt(ofst) => format!("JLT {}", ofst),
            Instr::Jgt(ofst) => format!("JGT {}", ofst),
            Instr::Jeq(ofst) => format!("JEQ {}", ofst),
        });
        code.push('\n');
    }

    code
}
