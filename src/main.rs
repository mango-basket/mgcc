#![allow(unused)]

use std::{
    fs::File,
    io::{self, stdin, stdout, Read, Write},
    process,
};

use clap::{ArgGroup, CommandFactory, Parser};
use lexer::Lexer;

use crate::codegen::{gen_code, gen_instrs};

mod codegen;
mod error;
mod lexer;
mod parser;

#[derive(Parser, Debug)]
#[command(name = "mango")]
#[command(group(
    ArgGroup::new("input")
        .required(true)
        .args(["file", "repl"]),
))]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[arg(value_name = "FILE")]
    input: Option<String>,

    #[arg(short, long)]
    repl: bool,

    #[arg(short, long, value_name = "OUTPUT", default_value = "out.nasm")]
    output: String,
}

fn main() -> io::Result<()> {
    let cli = Cli::parse();

    if cli.repl {
        // interactive mode
        loop {
            let mut input = String::new();
            print!("> ");
            stdout().flush()?;
            stdin().read_line(&mut input)?;
            let input = input.trim().to_string();

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
    } else if let Some(filename) = cli.input {
        // compile from file
        let mut code_file = File::open(&filename)?;
        let mut code = String::new();
        code_file.read_to_string(&mut code)?;

        match parser::parse(&mut Lexer::new(&code).peekable()) {
            Ok(ast) => match gen_instrs(ast) {
                Ok(instrs) => {
                    let mut output = File::create(&cli.output)?;
                    let code = gen_code(instrs);
                    output.write_all(code.as_bytes())?;
                }
                Err(err) => {
                    eprintln!("Compiling err: {}", err);
                    process::exit(1);
                }
            },
            Err(err) => {
                eprintln!("Parsing err: {}", err);
                process::exit(1);
            }
        }
    } else {
        Cli::command().print_help().unwrap();
        println!();
        process::exit(1);
    }

    Ok(())
}
