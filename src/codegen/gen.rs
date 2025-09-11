use std::collections::HashMap;

use crate::{
    codegen::{compiler::Compiler, Instr},
    error::CompilerResult,
    parser::Ast,
    type_check::VarEnv,
};

pub fn gen_asm(instrs: Vec<Instr>) -> String {
    let mut code = String::new();

    for instr in instrs {
        code.push_str(&match instr {
            Instr::Push(num) => format!("PUSH16 {}", num),
            Instr::Load(addr) => format!("LOAD8 {}", addr),
            Instr::Store(addr) => format!("STORE8 {}", addr),
            Instr::Halt => "HALT".into(),
            Instr::Add => "ADD".into(),
            Instr::Sub => "SUB".into(),
            Instr::Mul => "MUL".into(),
            Instr::Div => "DIV".into(),
            Instr::Neg => "NEG".into(),
            Instr::Not => "NOT".into(),
            Instr::Cmp => "CMP".into(),
            Instr::Jmp(ofst) => format!("JMP8 {}", ofst),
            Instr::Jlt(ofst) => format!("JLT8 {}", ofst),
            Instr::Jgt(ofst) => format!("JGT8 {}", ofst),
            Instr::Jeq(ofst) => format!("JEQ8 {}", ofst),
            Instr::Lbl(id) => format!("LBL{}:", id),
            Instr::JmpLbl(id) => format!("JMP LBL{}", id),
            Instr::JltLbl(id) => format!("JLT LBL{}", id),
            Instr::JgtLbl(id) => format!("JGT LBL{}", id),
            Instr::JeqLbl(id) => format!("JEQ LBL{}", id),
            Instr::And => "AND".into(),
            Instr::Or => "OR".into(),
            Instr::Xor => "XOR".into(),
            Instr::Shft => "SHFT".into(),
            Instr::Mov(rd, rs) => format!("MOV r{} r{}", rd, rs),
            Instr::Pushr(rs) => format!("PUSHR r{}", rs),
            Instr::Popr(rd) => format!("POPR r{}", rd),
            Instr::Loadp => "LOADP".into(),
            Instr::Storep => "STOREP".into(),
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
            Instr::Loadp => vec![0x12],
            Instr::Storep => vec![0x13],

            // Jumps and Branches
            Instr::Jmp(addr) => vec![0x20, (addr as u8)],
            Instr::Jlt(addr) => vec![0x21, (addr as u8)],
            Instr::Jgt(addr) => vec![0x22, (addr as u8)],
            Instr::Jeq(addr) => vec![0x23, (addr as u8)],

            // Integer Arithmetic
            Instr::Add => vec![0x30],
            Instr::Sub => vec![0x31],
            Instr::Mul => vec![0x32],
            Instr::Div => vec![0x33],
            Instr::Neg => vec![0x34],
            Instr::Cmp => vec![0x35],

            // Bitwise Ops
            Instr::Not => vec![0x40],
            Instr::And => vec![0x41],
            Instr::Or => vec![0x42],
            Instr::Xor => vec![0x43],
            Instr::Shft => vec![0x44],

            // Register operations
            Instr::Mov(rd, rs) => vec![0x50, (rd << 4) | rs],
            Instr::Pushr(rs) => vec![0x51, rs],
            Instr::Popr(rd) => vec![0x52, rd],

            // Labels
            _ => unreachable!(),
        });
    }

    code
}

pub fn gen_instrs<'ip>(ast: &'ip Ast<'ip>, var_env: VarEnv) -> CompilerResult<'ip, Vec<Instr>> {
    let mut compiler = Compiler {
        symbol_table: HashMap::new(),
        last_slot: 0,
        var_env,
        label_counter: 0,
        loop_stack: Vec::new(),
    };

    let mut ret = compiler.gen_instrs(ast)?;
    ret.push(Instr::Halt);
    Ok(ret)
}
