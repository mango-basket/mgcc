use std::collections::HashMap;

use computils::instr::Instr;

use crate::{
    codegen::ir_builder::{Compiler, FunctionContext},
    error::CompilerResult,
    grammar::ast::TypedAstNode,
};

fn reg(num: u8) -> String {
    match num {
        0..4 => format!("r{num}"),
        4 => format!("sp"),
        5 => format!("fp"),
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

pub fn gen_asm(instrs: Vec<Instr>) -> String {
    let mut prologue = vec![Instr::CallLbl("main".to_string()), Instr::Halt];
    prologue.extend(instrs.clone());
    let instrs = jmp_lbl_optimization(prologue);
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
            Instr::Mod => "MOD".into(),
            Instr::Jmp(ofst) => format!("JMP8 {}", ofst),
            Instr::Jlt(ofst) => format!("JLT8 {}", ofst),
            Instr::Jgt(ofst) => format!("JGT8 {}", ofst),
            Instr::Jeq(ofst) => format!("JEQ8 {}", ofst),
            Instr::Lbl(id) => format!("\n{}:", id),
            Instr::JmpLbl(id) => format!("JMP {}", id),
            Instr::JltLbl(id) => format!("JLT {}", id),
            Instr::JgtLbl(id) => format!("JGT {}", id),
            Instr::JeqLbl(id) => format!("JEQ {}", id),
            Instr::And => "AND".into(),
            Instr::Or => "OR".into(),
            Instr::Xor => "XOR".into(),
            Instr::Shft => "SHFT".into(),
            Instr::Mov(rd, rs) => format!("MOV {}, {}", reg(rd), reg(rs)),
            Instr::Pushr(rs) => format!("PUSHR {}", reg(rs)),
            Instr::Popr(rd) => format!("POPR {}", reg(rd)),
            Instr::Loadp => "LOADP".into(),
            Instr::Storep => "STOREP".into(),
            Instr::Call(ofst) => format!("CALL {}", ofst),
            Instr::Ret => "RET".into(),
            Instr::Print => "PRINT".into(),
            Instr::MvCur(ofst) => format!("MVCUR {}", ofst),
            Instr::CallLbl(id) => format!("CALL {}", id),
            Instr::Loadr(rs, imm) => format!("LOADR [{}, {}]", reg(rs), imm),
            Instr::Storer(rd, imm) => format!("STORER [{}, {}]", reg(rd), imm),
            Instr::Loadpb => "LOADPB".into(),
            Instr::Storepb => "STOREPB".into(),
        });
        code.push('\n');
    }

    code
}

pub fn gen_instrs<'ip>(
    ast: &'ip TypedAstNode<'ip>,
    functions: HashMap<String, FunctionContext>,
) -> CompilerResult<'ip, Vec<Instr>> {
    let mut compiler = Compiler {
        functions,
        label_counter: 0,
        loop_stack: Vec::new(),
        cur_func: None,
    };

    Ok(compiler.gen_instrs(ast)?)
}
