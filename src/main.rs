use std::io::{self, stdin, stdout, Write};

mod codegen;
mod error;
mod grammar;
mod semantic;
mod tokenizer;

use clap::{CommandFactory, Parser};
use tokenizer::lexer::Lexer;

use crate::{
    codegen::backend::{gen_asm, gen_instrs},
    grammar::parser,
    semantic::{analyzer::check_semantics, type_check::check_types},
};

#[derive(Parser, Debug)]
#[command(author, version, about)]
struct Cli {
    /// input files
    #[arg(value_name = "file")]
    input: Vec<String>,

    /// run in REPL mode
    #[arg(short, long)]
    repl: bool,

    /// emit assembly (`.masm`)
    #[arg(short = 'S', long)]
    asm: bool,

    /// dump the tokenstream instead of compiling
    #[arg(short = 't', long)]
    tokens: bool,

    /// dump the AST instead of compiling
    #[arg(short = 'A', long)]
    ast: bool,

    /// output filename
    #[arg(short, long)]
    output: Option<String>,
}

fn compile_source(code: &str, dump_tokens: bool, dump_ast: bool) -> Result<Vec<u8>, String> {
    let mut lexer = Lexer::new(code);

    if dump_tokens {
        for tok in lexer.by_ref() {
            println!("{:?}", tok);
        }
        return Ok(Vec::new());
    }

    let ast = parser::Parser::new(lexer, code)
        .parse()
        .map_err(|e| e.to_string())?;

    if dump_ast {
        println!("{}", ast.pretty(0));
        return Ok(Vec::new());
    }

    let (typed_ast, funcs) = check_types(&ast).map_err(|e| e.to_string())?;
    check_semantics(&typed_ast, &funcs).map_err(|e| e.to_string())?;
    let (instrs, data) = gen_instrs(&typed_ast, funcs).map_err(|e| e.to_string())?;

    Ok(gen_asm(instrs, data).into_bytes())
}

fn run_repl(dump_tokens: bool, dump_ast: bool) -> io::Result<()> {
    loop {
        print!("> ");
        stdout().flush()?;

        let mut input = String::new();
        stdin().read_line(&mut input)?;
        let input = input.trim();

        if input == "exit" {
            break;
        }

        match compile_source(input, dump_tokens, dump_ast) {
            Ok(bytes) => {
                if !dump_tokens && !dump_ast {
                    println!("{}", String::from_utf8_lossy(&bytes));
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
    dump_tokens: bool,
    dump_ast: bool,
) -> io::Result<()> {
    let code = std::fs::read_to_string(filename)?;

    match compile_source(&code, dump_tokens, dump_ast) {
        Ok(bytes) => {
            if !dump_tokens && !dump_ast {
                std::fs::write(output_path, bytes)?;
            }
        }
        Err(err) => {
            eprintln!("Compilation failed: {}", err);
            std::process::exit(1);
        }
    }

    Ok(())
}

fn main() -> io::Result<()> {
    let cli = Cli::parse();

    if cli.repl {
        return run_repl(cli.tokens, cli.ast);
    }

    if let Some(filename) = cli.input.get(0) {
        let output = cli
            .output
            .clone()
            .unwrap_or_else(|| format!("{}.masm", filename));
        compile_file(filename, &output, cli.tokens, cli.ast)?;
        return Ok(());
    }

    Cli::command().print_help()?;
    println!();
    std::process::exit(1);
}
