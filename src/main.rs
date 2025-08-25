use std::{
    fs::File,
    io::{self, stdin, stdout, Read, Write},
    process,
};

mod codegen;
mod error;
mod lexer;
mod parser;
mod type_check;

use clap::{ArgGroup, CommandFactory, Parser};
use lexer::Lexer;

use crate::{
    codegen::{gen_code, gen_instrs},
    type_check::check_types,
};

#[derive(Parser, Debug)]
#[command(name = "mango")]
#[command(group(
    ArgGroup::new("source")
        .required(true)
        .args(["input", "repl"]),
))]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[arg(value_name = "FILE")]
    input: Option<String>,

    #[arg(short, long)]
    repl: bool,

    #[arg(short, long, value_name = "OUTPUT", default_value = "out.masm")]
    output: String,
}

fn run_repl() -> io::Result<()> {
    loop {
        let mut input = String::new();
        print!("> ");
        stdout().flush()?;
        stdin().read_line(&mut input)?;
        let input = input.trim();

        if input == "exit" {
            break;
        }

        match parser::parse(&mut Lexer::new(input).peekable())
            .and_then(|ast| check_types(ast))
            .and_then(|(ast, type_env, var_env)| gen_instrs(ast, type_env, var_env))
        {
            Ok(instrs) => println!("{}", gen_code(instrs)),
            Err(err) => eprintln!("Error: {}", err),
        }
    }
    Ok(())
}

fn compile_file(filename: &str, output_path: &str) -> io::Result<()> {
    let mut code_file = File::open(filename)?;
    let mut code = String::new();
    code_file.read_to_string(&mut code)?;

    match parser::parse(&mut Lexer::new(&code).peekable())
        .and_then(|ast| check_types(ast))
        .and_then(|(ast, type_env, var_env)| gen_instrs(ast, type_env, var_env))
    {
        Ok(instrs) => {
            let mut output = File::create(output_path)?;
            output.write_all(gen_code(instrs).as_bytes())?;
        }
        Err(err) => {
            eprintln!("Compilation failed: {}", err);
            process::exit(1);
        }
    }

    Ok(())
}

fn main() -> io::Result<()> {
    let cli = Cli::parse();

    if cli.repl {
        run_repl()
    } else if let Some(filename) = cli.input {
        compile_file(&filename, &cli.output)
    } else {
        Cli::command().print_help().unwrap();
        println!();
        process::exit(1);
    }
}
