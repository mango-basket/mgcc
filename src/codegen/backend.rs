use std::collections::HashMap;

use computils::instr::Instr;

use crate::{
    codegen::ir_builder::{Compiler, FunctionContext},
    error::CompilerResult,
    grammar::ast::Ast,
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
            Instr::Lbl(id) => format!("\n{}:", id),
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
            Instr::Call(ofst) => format!("CALL {}", ofst),
            Instr::Ret => "RET".into(),
            Instr::Print => "PRINT".into(),
            Instr::MvCur(ofst) => format!("MVCUR {}", ofst),
            Instr::CallLbl(id) => format!("CALL {}", id),
            Instr::Loadr(rs, imm) => format!("LOADR [r{}, {}]", rs, imm),
            Instr::Storer(rd, imm) => format!("STORER [r{}, {}]", rd, imm),
        });
        code.push('\n');
    }

    code
}

pub fn gen_instrs<'ip>(
    ast: &'ip Ast<'ip>,
    functions: HashMap<String, FunctionContext>,
) -> CompilerResult<'ip, Vec<Instr>> {
    let mut compiler = Compiler {
        functions,
        label_counter: 0,
        loop_stack: Vec::new(),
        cur_func: None,
    };

    let mut ret = compiler.gen_instrs(ast)?;
    ret.push(Instr::Halt);
    Ok(ret)
}
