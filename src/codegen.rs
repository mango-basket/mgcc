use crate::{
    error::{CompilerError, CompilerResult},
    lexer::{Token, TokenKind},
    parser::Ast,
};

pub enum Instr {
    Push(i64),
    Pop,
    Add,
    Sub,
    Mul,
    Div,
    Neg,
    Halt,
}

pub fn gen_instrs<'ip>(ast: Ast<'ip>) -> CompilerResult<'ip, Vec<Instr>> {
    let mut ret = _gen_instrs(ast)?;
    ret.push(Instr::Halt);
    Ok(ret)
}

fn _gen_instrs<'ip>(ast: Ast<'ip>) -> CompilerResult<'ip, Vec<Instr>> {
    let mut instrs = Vec::new();

    match ast {
        Ast::Uint(tok) => {
            if let TokenKind::Uint(num) = tok.kind {
                instrs.push(Instr::Push(num as i64))
            } else {
                unreachable!()
            }
        }
        Ast::UnaryOp { op, operand } => {
            instrs.extend(_gen_instrs(*operand)?);
            match op.kind {
                TokenKind::Plus => {}
                TokenKind::Minus => instrs.push(Instr::Neg),
                _ => {
                    return Err(CompilerError::UnexpectedToken {
                        got: op,
                        expected: "-' or '+",
                    })
                }
            }
        }
        Ast::BinaryOp { left, op, right } => {
            instrs.extend(_gen_instrs(*left)?);
            instrs.extend(_gen_instrs(*right)?);

            instrs.push(match op.kind {
                TokenKind::Plus => Instr::Add,
                TokenKind::Minus => Instr::Sub,
                TokenKind::Star => Instr::Mul,
                TokenKind::Slash => Instr::Div,
                _ => {
                    return Err(CompilerError::UnexpectedToken {
                        got: op,
                        expected: "+', '-', '*' or '/",
                    })
                }
            })
        }
        _ => {}
    }

    Ok(instrs)
}

pub fn gen_code(instrs: Vec<Instr>) -> String {
    let mut code = String::new();

    for instr in instrs {
        code.push_str(&match instr {
            Instr::Push(num) => format!("PUSH {}", num),
            Instr::Pop => "POP".into(),
            Instr::Add => "ADD".into(),
            Instr::Sub => "SUB".into(),
            Instr::Mul => "MUL".into(),
            Instr::Div => "DIV".into(),
            Instr::Neg => "NEG".into(),
            Instr::Halt => "HALT".into(),
        });
        code.push('\n');
    }

    code
}
