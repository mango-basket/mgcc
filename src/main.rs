#![allow(unused)]

use std::{
    env,
    fs::File,
    io::{self, stdin, stdout, Read, Write},
};

use lexer::Lexer;

use crate::codegen::{gen_code, gen_instrs};

mod codegen;
mod error;
mod lexer;
mod parser;

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();

    if args.len() > 1 {
        let mut code_file = File::open(&args[1])?;
        let mut code = String::new();
        code_file.read_to_string(&mut code)?;

        match parser::parse(&mut Lexer::new(&code).peekable()) {
            Ok(ast) => match gen_instrs(ast) {
                Ok(instrs) => {
                    let mut output = File::create("out.nasm")?;
                    let code = gen_code(instrs);
                    output.write(code.as_bytes())?;
                }
                Err(err) => println!("Compiling err: {}", err),
            },
            Err(err) => println!("Parsing err: {}", err),
        }
    } else {
        loop {
            let mut input = String::new();
            print!("> ");
            stdout().flush()?;
            stdin().read_line(&mut input)?;
            input = input.trim().to_string();

            if input == "exit" {
                break;
            }

            match parser::parse(&mut Lexer::new(&input).peekable()) {
                Ok(ast) => match gen_instrs(ast) {
                    Ok(instrs) => {
                        let code = gen_code(instrs);
                        println!("{}", code);
                    }
                    Err(err) => println!("Compiling err: {}", err),
                },
                Err(err) => println!("Parsing err: {}", err),
            }
        }
    }
    Ok(())
}
