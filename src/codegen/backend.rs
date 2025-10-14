use std::collections::HashMap;

use computils::instr::Instr;

use crate::{
    codegen::ir_builder::{Compiler, FunctionContext},
    error::CompilerResult,
    grammar::ast::TypedAstNode,
};

fn reg(num: u8) -> String {
    match num {
        0..=7 => format!("r{num}"),
        8 => format!("sp"),
        9 => format!("fp"),
        _ => unreachable!(),
    }
}

fn jmp_lbl_optimization(instrs: Vec<Instr>) -> Vec<Instr> {
    use std::collections::HashMap;

    let mut out = Vec::new();
    let mut label_aliases: HashMap<String, String> = HashMap::new();

    // pass 1: eliminate useless jumps, detect label merges
    let mut i = 0;
    while i < instrs.len() {
        match &instrs[i] {
            // case: JMP lbl immediately followed by lbl
            Instr::JmpLbl(jlbl) => {
                if i + 1 < instrs.len() {
                    if let Instr::Lbl(lbl) = &instrs[i + 1] {
                        if jlbl == lbl {
                            // useless jump, skip it
                            i += 1; // skip JMP
                            continue;
                        }
                    }
                }
                out.push(instrs[i].clone());
            }

            // case: duplicate labels — record alias
            Instr::Lbl(name) => {
                if let Some(Instr::Lbl(prev)) = out.last() {
                    // last instr was also a label at same spot
                    label_aliases.insert(name.clone(), prev.clone());
                    // don’t emit duplicate label
                } else {
                    out.push(instrs[i].clone());
                }
            }

            other => out.push(other.clone()),
        }
        i += 1;
    }

    // pass 2: rewrite jumps to use canonical labels
    let mut final_out = Vec::new();
    for instr in out {
        match instr {
            Instr::JmpLbl(id) => {
                let target = resolve_alias(&id, &label_aliases);
                final_out.push(Instr::JmpLbl(target));
            }
            Instr::JltLbl(id) => {
                let target = resolve_alias(&id, &label_aliases);
                final_out.push(Instr::JltLbl(target));
            }
            Instr::JgtLbl(id) => {
                let target = resolve_alias(&id, &label_aliases);
                final_out.push(Instr::JgtLbl(target));
            }
            Instr::JeqLbl(id) => {
                let target = resolve_alias(&id, &label_aliases);
                final_out.push(Instr::JeqLbl(target));
            }
            Instr::CallLbl(id) => {
                let target = resolve_alias(&id, &label_aliases);
                final_out.push(Instr::CallLbl(target));
            }
            Instr::Lbl(id) => {
                let target = resolve_alias(&id, &label_aliases);
                final_out.push(Instr::Lbl(target));
            }
            other => final_out.push(other),
        }
    }

    final_out
}

fn resolve_alias(name: &str, aliases: &HashMap<String, String>) -> String {
    let mut cur = name;
    while let Some(next) = aliases.get(cur) {
        cur = next;
    }
    cur.to_string()
}

pub fn gen_asm(instrs: Vec<Instr>, data: HashMap<String, String>) -> String {
    let mut code = String::new();

    code.push_str("@section data\n");
    for (n, raw) in data.iter() {
        code.push_str(&format!("{n} = {raw}\n"));
    }

    code.push_str("@section text\n");

    let mut prologue = vec![Instr::CallLbl("main".to_string()), Instr::Halt];

    prologue.extend(instrs.clone());
    let instrs = jmp_lbl_optimization(prologue);

    for instr in instrs {
        code.push_str(&match instr {
            Instr::Push(num) => format!("PUSH16 {}", num),
            Instr::Halt => "HALT".into(),
            Instr::Add => "ADD".into(),
            Instr::Sub => "SUB".into(),
            Instr::Mul => "MUL".into(),
            Instr::Div => "DIV".into(),
            Instr::Neg => "NEG".into(),
            Instr::Not => "NOT".into(),
            Instr::Cmp => "CMP".into(),
            Instr::Mod => "MOD".into(),
            Instr::Jmp(ofst) => format!("JMP16 {}", ofst),
            Instr::Jlt(ofst) => format!("JLT16 {}", ofst),
            Instr::Jgt(ofst) => format!("JGT16 {}", ofst),
            Instr::Jeq(ofst) => format!("JEQ16 {}", ofst),
            Instr::Lbl(id) => format!("\n{}:", id),
            Instr::JmpLbl(id) => format!("JMP {}", id),
            Instr::JltLbl(id) => format!("JLT {}", id),
            Instr::JgtLbl(id) => format!("JGT {}", id),
            Instr::JeqLbl(id) => format!("JEQ {}", id),
            Instr::And => "AND".into(),
            Instr::Or => "OR".into(),
            Instr::Xor => "XOR".into(),
            Instr::Shl => "SHL".into(),
            Instr::Shr => "SHR".into(),
            Instr::Mov(rd, rs) => format!("MOV {}, {}", reg(rd), reg(rs)),
            Instr::Pushr(rs) => format!("PUSHR {}", reg(rs)),
            Instr::Popr(rd) => format!("POPR {}", reg(rd)),
            Instr::Ldw => "LDW".into(),
            Instr::Stw => "STW".into(),
            Instr::Call(ofst) => format!("CALL {}", ofst),
            Instr::Ret => "RET".into(),
            Instr::CallLbl(id) => format!("CALL {}", id),
            Instr::Ldr(rs, imm) => format!("LDR [{}, {}]", reg(rs), imm),
            Instr::Str(rd, imm) => format!("STR [{}, {}]", reg(rd), imm),
            Instr::Ldb => "LDB".into(),
            Instr::Stb => "STB".into(),
            Instr::Data(lbl) => format!("DATA {}", lbl),
            Instr::Int(int) => format!("INT {}", int),
            Instr::Iret => "IRET".into(),
            Instr::Bkpt => "BKPT".into(),
            Instr::CmpI(imm) => format!("CMPI {}", imm),
            Instr::AddI(imm) => format!("ADDI {}", imm),
            Instr::SubI(imm) => format!("SUBI {}", imm),
            Instr::MulI(imm) => format!("MULI {}", imm),
            Instr::DivI(imm) => format!("DIVI {}", imm),
            Instr::NegI(imm) => format!("NEGI {}", imm),
            Instr::ModI(imm) => format!("MODI {}", imm),
            Instr::NotI(imm) => format!("NOTI {}", imm),
            Instr::AndI(imm) => format!("ANDI {}", imm),
            Instr::OrI(imm) => format!("ORI {}", imm),
            Instr::XorI(imm) => format!("XORI {}", imm),
            Instr::ShlI(imm) => format!("SHLI {}", imm),
            Instr::ShrI(imm) => format!("SHRI {}", imm),
        });
        code.push('\n');
    }

    code
}

pub fn gen_instrs<'ip>(
    ast: &'ip TypedAstNode<'ip>,
    functions: HashMap<String, FunctionContext>,
) -> CompilerResult<'ip, (Vec<Instr>, HashMap<String, String>)> {
    let mut compiler = Compiler {
        functions,
        label_counter: 0,
        data_counter: 0,
        data_strings: HashMap::new(),
        loop_stack: Vec::new(),
        cur_func: None,
    };

    Ok((compiler.gen_instrs(ast)?, compiler.data_strings))
}
