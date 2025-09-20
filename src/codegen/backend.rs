use std::collections::HashMap;

use computils::instr::Instr;

use crate::{
    codegen::ir_builder::{Compiler, FunctionContext},
    error::CompilerResult,
    grammar::ast::AstNode,
};

fn reg(num: u8) -> String {
    match num {
        0..4 => format!("r{num}"),
        4 => format!("sp"),
        5 => format!("fp"),
        _ => unreachable!(),
    }
}

pub fn gen_asm(instrs: Vec<Instr>) -> String {
    let mut prologue = vec![Instr::CallLbl("main".to_string()), Instr::Halt];
    prologue.extend(instrs.clone());
    let instrs = prologue;
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
        });
        code.push('\n');
    }

    code
}

pub fn gen_instrs<'ip>(
    ast: &'ip AstNode<'ip>,
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
