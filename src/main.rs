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

fn run_repl(emit_asm: bool) -> io::Result<()> {
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
            Ok(instrs) => {
                if emit_asm {
                    println!("{}", gen_asm(instrs));
                } else {
                    let bin = gen_bin(instrs);
                    println!("{:02X?}", bin);
                }
            }
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
    let mut code_file = File::open(filename)?;
    let mut code = String::new();
    code_file.read_to_string(&mut code)?;

    let mut lexer = Lexer::new(&code).peekable();

    if dump_tokens {
        for tok in lexer.by_ref() {
            println!("{:?}", tok);
        }
        return Ok(());
    }

    match parser::parse(&mut lexer)
        .and_then(|ast| {
            if dump_ast {
                println!("{:#?}", ast);
                return Ok((ast, Default::default(), Default::default())); // fake envs so typecheck doesn’t run
            }
            check_types(ast)
        })
        .and_then(|(ast, type_env, var_env)| gen_instrs(ast, type_env, var_env))
    {
        Ok(instrs) => {
            let mut output = File::create(output_path)?;
            if emit_asm {
                output.write_all(gen_asm(instrs).as_bytes())?;
            } else {
                output.write_all(&gen_bin(instrs))?;
            }
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

    let emit_asm = cli.asm;
    let dump_tokens = cli.tokens;
    let dump_ast = cli.ast;

    let output = cli.output.unwrap_or_else(|| {
        if emit_asm {
            "out.masm".to_string()
        } else {
            "out.mbin".to_string()
        }
    });

    if cli.repl {
        run_repl(emit_asm)
    } else if let Some(filename) = cli.input {
        compile_file(&filename, &output, emit_asm, dump_tokens, dump_ast)
    } else {
        Cli::command().print_help().unwrap();
        println!();
        process::exit(1);
    }
}
