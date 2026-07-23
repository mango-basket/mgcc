#![allow(unused)]

use std::io::{self, stdin, stdout, Write};

mod codegen;
mod error;
mod grammar;
mod optimizer;
mod semantic;
mod tokenizer;

use clap::{CommandFactory, Parser};
use tokenizer::lexer::Lexer;

use crate::{
    codegen::backend::{gen_asm, gen_instrs},
    codegen::mif::gen_mif,
    grammar::ast::{TypedAstKind, TypedAstNode},
    grammar::parser,
    optimizer::fold,
    semantic::{analyzer::check_semantics, type_check::check_types},
};

fn extract_module_name(ast: &TypedAstNode<'_>) -> Option<String> {
    match &ast.kind {
        TypedAstKind::Module(name) => Some(name.span.get_str().to_string()),
        TypedAstKind::Items(items) => {
            for item in items {
                if let Some(name) = extract_module_name(item) {
                    return Some(name);
                }
            }
            None
        }
        TypedAstKind::Statements(stmts) => {
            for stmt in stmts {
                if let Some(name) = extract_module_name(stmt) {
                    return Some(name);
                }
            }
            None
        }
        _ => None,
    }
}

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

    /// compile as library (skip main enforcement, emit .mif)
    #[arg(long)]
    lib: bool,
}

fn compile_source(
    code: &str,
    dump_tokens: bool,
    dump_ast: bool,
    lib: bool,
    module_name: &str,
) -> Result<(Vec<u8>, Option<String>), String> {
    let mut lexer = Lexer::new(code);

    if dump_tokens {
        for tok in lexer.by_ref() {
            println!("{:?}", tok);
        }
        return Ok((Vec::new(), None));
    }

    let ast = parser::Parser::new(lexer, code)
        .parse()
        .map_err(|e| e.to_string())?;

    if dump_ast {
        println!("{:#?}", ast);
        return Ok((Vec::new(), None));
    }

    let (mut typed_ast, funcs) = check_types(&ast).map_err(|e| e.to_string())?;
    check_semantics(&typed_ast, &funcs, lib).map_err(|e| e.to_string())?;
    let folded_ast = fold(&typed_ast).map_err(|e| e.to_string())?;
    let (instrs, data) = gen_instrs(&folded_ast, funcs.clone()).map_err(|e| e.to_string())?;

    let asm = gen_asm(instrs, data, lib);

    let mif = if lib {
        let mod_name = extract_module_name(&folded_ast).unwrap_or_else(|| module_name.to_string());
        Some(gen_mif(&folded_ast, &funcs, &mod_name))
    } else {
        None
    };

    Ok((asm.into_bytes(), mif))
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

        match compile_source(input, dump_tokens, dump_ast, false, "<repl>") {
            Ok((bytes, _)) => {
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
    lib: bool,
) -> io::Result<()> {
    let code = std::fs::read_to_string(filename)?;

    let module_name = std::path::Path::new(filename)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("module");

    match compile_source(&code, dump_tokens, dump_ast, lib, module_name) {
        Ok((bytes, mif)) => {
            if !dump_tokens && !dump_ast {
                std::fs::write(output_path, bytes)?;
            }
            if let Some(mif_text) = mif {
                let mif_path = if output_path.ends_with(".masm") {
                    format!("{}.mif", &output_path[..output_path.len() - 5])
                } else {
                    format!("{}.mif", output_path)
                };
                std::fs::write(&mif_path, mif_text)?;
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
        compile_file(filename, &output, cli.tokens, cli.ast, cli.lib)?;
        return Ok(());
    }

    Cli::command().print_help()?;
    println!();
    std::process::exit(1);
}
