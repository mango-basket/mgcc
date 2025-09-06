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

use clap::{CommandFactory, Parser};
use lexer::Lexer;

use crate::{
    codegen::{gen_asm, gen_bin, gen_instrs},
    type_check::check_types,
};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// input file
    #[arg(value_name = "test.mg")]
    input: Option<String>,

    /// run in REPL mode
    #[arg(short, long)]
    repl: bool,

    /// emit assembly (`out.masm` default)
    #[arg(short = 'S', long)]
    asm: bool,

    /// dump the tokenstream instead of compiling
    #[arg(short = 't', long)]
    tokens: bool,

    /// dump the AST instead of compiling
    #[arg(short = 'A', long)]
    ast: bool,

    /// output filename
    #[arg(short, long, value_name = "a.out")]
    output: Option<String>,
}

enum OutputKind {
    Bytes(Vec<u8>),
    Tokens,
    Ast,
}

fn compile_source(
    code: &str,
    emit_asm: bool,
    dump_tokens: bool,
    dump_ast: bool,
) -> Result<OutputKind, String> {
    let mut lexer = Lexer::new(code);

    if dump_tokens {
        for tok in lexer.by_ref() {
            println!("{:?}", tok);
        }
        return Ok(OutputKind::Tokens);
    }

    let ast = parser::Parser::new(lexer)
        .parse()
        .map_err(|e| e.to_string())?;

    if dump_ast {
        println!("{:#?}", ast);
        return Ok(OutputKind::Ast);
    }

    let (ast, var_env) = check_types(ast).map_err(|e| e.to_string())?;
    let instrs = gen_instrs(ast, var_env).map_err(|e| e.to_string())?;

    if emit_asm {
        Ok(OutputKind::Bytes(gen_asm(instrs).into_bytes()))
    } else {
        Ok(OutputKind::Bytes(gen_bin(instrs)))
    }
}

fn run_repl(emit_asm: bool) -> io::Result<()> {
    loop {
        print!("> ");
        stdout().flush()?;

        let mut input = String::new();
        stdin().read_line(&mut input)?;
        let input = input.trim();

        if input == "exit" {
            break;
        }

        match compile_source(input, emit_asm, false, false) {
            Ok(OutputKind::Bytes(bytes)) => {
                if emit_asm {
                    println!("{}", String::from_utf8_lossy(&bytes));
                } else {
                    println!("{:02X?}", bytes);
                }
            }
            Ok(OutputKind::Tokens) | Ok(OutputKind::Ast) => {}
            Err(err) => eprintln!("Error: {}", err),
        }
    }
    Ok(())
}

fn compile_file(
    filename: &str,
    output_path: &str,
    emit_asm: bool,
    dump_tokens: bool,
    dump_ast: bool,
) -> io::Result<()> {
    let mut code = String::new();
    File::open(filename)?.read_to_string(&mut code)?;

    match compile_source(&code, emit_asm, dump_tokens, dump_ast) {
        Ok(OutputKind::Bytes(bytes)) => File::create(output_path)?.write_all(&bytes)?,
        Ok(OutputKind::Tokens) | Ok(OutputKind::Ast) => {}
        Err(err) => {
            eprintln!("Compilation failed: {}", err);
            process::exit(1);
        }
    }

    Ok(())
}

fn main() -> io::Result<()> {
    let cli = Cli::parse();

    let output = cli.output.unwrap_or_else(|| {
        if cli.asm {
            "out.masm".into()
        } else {
            "out.mbin".into()
        }
    });

    if cli.repl {
        run_repl(cli.asm)
    } else if let Some(filename) = cli.input {
        compile_file(&filename, &output, cli.asm, cli.tokens, cli.ast)
    } else {
        Cli::command().print_help().unwrap();
        println!();
        process::exit(1);
    }
}
