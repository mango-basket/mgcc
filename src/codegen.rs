use std::collections::HashMap;

use crate::{
    error::{CompilerError, CompilerResult},
    lexer::TokenKind,
    parser::Ast,
    type_check::{Type, VarEnv},
};

pub enum Instr {
    Push(u16),
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

    // label pseudo instructions
    Lbl(usize),
    JmpLbl(usize),
    JltLbl(usize),
    JgtLbl(usize),
    JeqLbl(usize),
}

impl Instr {
    fn byte_len(&self) -> usize {
        match self {
            Instr::Push(_) => 3, // opcode + 2-byte immediate
            Instr::Load(_) => 2, // opcode + 1-byte addr
            Instr::Store(_) => 2,
            Instr::Jmp(_) => 2,
            Instr::Jlt(_) => 2,
            Instr::Jgt(_) => 2,
            Instr::Jeq(_) => 2,
            Instr::Iadd
            | Instr::Isub
            | Instr::Imul
            | Instr::Idiv
            | Instr::Neg
            | Instr::Not
            | Instr::Icmp
            | Instr::Halt => 1,

            // pseudo-instructions (labels don’t emit bytes)
            Instr::Lbl(_) => 0,
            Instr::JmpLbl(_) => 2, // these will turn into a JMP8
            Instr::JltLbl(_) => 2,
            Instr::JgtLbl(_) => 2,
            Instr::JeqLbl(_) => 2,
        }
    }
}

type SymbolTable = HashMap<String, (u8, Type)>;

struct Compiler {
    symbol_table: SymbolTable,
    last_slot: u8,
    var_env: VarEnv,
    label_counter: usize,
}

pub fn gen_instrs<'ip>(ast: Ast<'ip>, var_env: VarEnv) -> CompilerResult<'ip, Vec<Instr>> {
    let mut compiler = Compiler {
        symbol_table: HashMap::new(),
        last_slot: 0,
        var_env,
        label_counter: 0,
    };

    let mut ret = compiler.gen_instrs(ast)?;
    ret.push(Instr::Halt);
    Ok(ret)
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
                instrs.push(Instr::JeqLbl(lbl_true)); // equal → true
            }
            TokenKind::Neq => {
                // not equal → jump to true if NOT zero
                // easiest: jump if equal → skip true
                instrs.push(Instr::JeqLbl(lbl_end));
                instrs.push(Instr::JmpLbl(lbl_true));
            }
            TokenKind::Lt => {
                instrs.push(Instr::JltLbl(lbl_true)); // < → true
            }
            TokenKind::Gt => {
                instrs.push(Instr::JgtLbl(lbl_true)); // > → true
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
                    TokenKind::Eq
                    | TokenKind::Neq
                    | TokenKind::Lt
                    | TokenKind::Gt
                    | TokenKind::Lte
                    | TokenKind::Gte => instrs.extend(self.gen_comparison(op.kind)),

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
            Ast::Assign {
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
        }

        Ok(instrs)
    }
}

pub fn gen_asm(instrs: Vec<Instr>) -> String {
    let mut code = String::new();

    for instr in instrs {
        code.push_str(&match instr {
            Instr::Push(num) => format!("PUSH16 {}", num),
            Instr::Load(addr) => format!("LOAD8 {}", addr),
            Instr::Store(addr) => format!("STORE8 {}", addr),
            Instr::Halt => "HALT".into(),
            Instr::Iadd => "IADD".into(),
            Instr::Isub => "ISUB".into(),
            Instr::Imul => "IMUL".into(),
            Instr::Idiv => "IDIV".into(),
            Instr::Neg => "NEG".into(),
            Instr::Not => "NOT".into(),
            Instr::Icmp => "ICMP".into(),
            Instr::Jmp(ofst) => format!("JMP8 {}", ofst),
            Instr::Jlt(ofst) => format!("JLT8 {}", ofst),
            Instr::Jgt(ofst) => format!("JGT8 {}", ofst),
            Instr::Jeq(ofst) => format!("JEQ8 {}", ofst),
            Instr::Lbl(id) => format!("LBL{}:", id),
            Instr::JmpLbl(id) => format!("JMP LBL{}", id),
            Instr::JltLbl(id) => format!("JLT LBL{}", id),
            Instr::JgtLbl(id) => format!("JGT LBL{}", id),
            Instr::JeqLbl(id) => format!("JEQ LBL{}", id),
        });
        code.push('\n');
    }

    code
}

pub fn resolve_labels(instrs: Vec<Instr>) -> Vec<Instr> {
    let mut offsets = HashMap::new();
    let mut byte_pos = 0;

    // first pass: record byte offsets of labels
    for instr in &instrs {
        match instr {
            Instr::Lbl(id) => {
                offsets.insert(*id, byte_pos);
            }
            _ => byte_pos += instr.byte_len(),
        }
    }

    // second pass: generate real instructions with resolved offsets
    let mut resolved = Vec::new();
    byte_pos = 0;

    for instr in instrs {
        match instr {
            Instr::Lbl(_) => {
                // labels don't emit bytes
            }
            Instr::JmpLbl(id) => {
                let target = offsets[&id];
                let rel = target as isize - (byte_pos as isize + 2); // JMP8 is 2 bytes
                resolved.push(Instr::Jmp(rel as i8));
                byte_pos += 2;
            }
            Instr::JltLbl(id) => {
                let target = offsets[&id];
                let rel = target as isize - (byte_pos as isize + 2); // JLT8 is 2 bytes
                resolved.push(Instr::Jlt(rel as i8));
                byte_pos += 2;
            }
            Instr::JgtLbl(id) => {
                let target = offsets[&id];
                let rel = target as isize - (byte_pos as isize + 2);
                resolved.push(Instr::Jgt(rel as i8));
                byte_pos += 2;
            }
            Instr::JeqLbl(id) => {
                let target = offsets[&id];
                let rel = target as isize - (byte_pos as isize + 2);
                resolved.push(Instr::Jeq(rel as i8));
                byte_pos += 2;
            }
            other => {
                byte_pos += other.byte_len();
                resolved.push(other);
            }
        }
    }

    resolved
}

pub fn gen_bin(instrs: Vec<Instr>) -> Vec<u8> {
    let instrs = resolve_labels(instrs);
    let mut code = Vec::new();

    for instr in instrs {
        code.extend(match instr {
            // Stack and control
            Instr::Push(addr) => vec![0x01, (addr & 0xFF) as u8, (addr >> 8) as u8], // LE
            Instr::Halt => vec![0x0F],

            // Memory
            Instr::Load(addr) => vec![0x10, addr],
            Instr::Store(addr) => vec![0x11, addr],

            // Jumps and Branches
            Instr::Jmp(addr) => vec![0x20, (addr as u8)],
            Instr::Jlt(addr) => vec![0x21, (addr as u8)],
            Instr::Jgt(addr) => vec![0x22, (addr as u8)],
            Instr::Jeq(addr) => vec![0x23, (addr as u8)],

            // Integer Arithmetic
            Instr::Iadd => vec![0x30],
            Instr::Isub => vec![0x31],
            Instr::Imul => vec![0x32],
            Instr::Idiv => vec![0x33],
            Instr::Neg => vec![0x34],
            Instr::Icmp => vec![0x35],

            // Logical Ops
            Instr::Not => vec![0x40],

            // Labels
            _ => unreachable!(),
        });
    }

    code
}
