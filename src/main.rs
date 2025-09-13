use std::{
    fs::File,
    io::{self, stdin, stdout, Read, Write},
    process,
};

mod codegen;
mod error;
mod lexer;
mod parser;
mod semantic;

use clap::{CommandFactory, Parser};
use lexer::Lexer;

use crate::{
    codegen::{
        assembler::{assemble_object, parse_assembly},
        backend::{gen_asm, gen_instrs},
        instr::Instr,
        linker::link_objects,
    },
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

    /// produce object file (`.mobj`) from source or assembly
    #[arg(short = 'O', long)]
    object: bool,

    /// link object files into binary (`a.out` default)
    #[arg(short = 'L', long)]
    link: bool,

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
        println!("{}", ast.pretty(0));
        return Ok(OutputKind::Ast);
    }

    let var_env = check_types(&ast).map_err(|e| e.to_string())?;
    check_semantics(&ast).map_err(|e| e.to_string())?;
    let instrs = gen_instrs(&ast, var_env).map_err(|e| e.to_string())?;

    if emit_asm {
        Ok(OutputKind::Bytes(gen_asm(instrs).into_bytes()))
    } else {
        let object = assemble_object(&instrs).unwrap();
        let instrs = link_objects(vec![object, get_print_object()]).unwrap();
        Ok(OutputKind::Bytes(instrs))
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

// TEMP
fn get_print_object() -> Vec<u8> {
    // temporarily hardcoding print
    let print_unsigned: Vec<Instr> = vec![
        Instr::Lbl("print".into()),
        // check if r0 == 0
        Instr::Pushr(0),
        Instr::Push(0),
        Instr::Cmp,
        Instr::JeqLbl("print_zero".into()),
        // loop: extract digits and push to stack
        Instr::Lbl("loop".into()),
        Instr::Pushr(0), // save current r0
        Instr::Pushr(0), // save current r0
        Instr::Push(10),
        Instr::Div,      // quotient = r0 / 10
        Instr::Popr(0),  // update r0 = quotient
        Instr::Pushr(0), // push quotient * 10
        Instr::Push(10),
        Instr::Mul,
        Instr::Sub,      // remainder = old_value - quotient*10
        Instr::Popr(1),  // remainder in r1
        Instr::Pushr(1), // push remainder ascii to stack
        Instr::Push(0x30),
        Instr::Add,
        Instr::Pushr(2),
        Instr::Push(1),
        Instr::Add,
        Instr::Popr(2), // inc r2
        // check if quotient != 0, else break
        Instr::Pushr(0),
        Instr::Push(0),
        Instr::Cmp,
        Instr::JeqLbl("print_digits".into()),
        Instr::JmpLbl("loop".into()),
        // print digits from stack (now in correct order)
        Instr::Lbl("print_digits".into()),
        Instr::Pushr(2),
        Instr::Push(1),
        Instr::Sub,
        Instr::Popr(2),
        Instr::Print,
        Instr::Pushr(2),
        Instr::Push(0),
        Instr::Cmp,
        Instr::JeqLbl("end".into()),
        Instr::JmpLbl("print_digits".into()),
        // handle zero
        Instr::Lbl("print_zero".into()),
        Instr::Push(0x30),
        Instr::Print,
        Instr::Lbl("end".into()),
        // Print newline
        Instr::Push(10),
        Instr::Print,
        Instr::Ret,
    ];

    assemble_object(&print_unsigned).unwrap()
}

fn default_output_name(input: &str, ext: &str) -> String {
    let path = std::path::Path::new(input);
    let stem = path
        .file_stem()
        .unwrap_or_else(|| std::ffi::OsStr::new("out"));
    let parent = path.parent().unwrap_or_else(|| std::path::Path::new(""));
    let filename = format!("{}.{}", stem.to_string_lossy(), ext);
    if parent.as_os_str().is_empty() {
        filename
    } else {
        parent.join(filename).to_string_lossy().to_string()
    }
}

fn main() -> io::Result<()> {
    let cli = Cli::parse();

    if cli.repl {
        return run_repl(cli.asm);
    }

    // determine output filename
    let output = if let Some(out) = cli.output.clone() {
        out
    } else if cli.asm {
        cli.input
            .get(0)
            .map(|f| default_output_name(f, "masm"))
            .unwrap_or_else(|| "out.masm".into())
    } else if cli.object {
        cli.input
            .get(0)
            .map(|f| default_output_name(f, "mobj"))
            .unwrap_or_else(|| "out.mobj".into())
    } else if cli.link {
        "a.out".into()
    } else {
        cli.input
            .get(0)
            .map(|f| default_output_name(f, "mbin"))
            .unwrap_or_else(|| "a.out".into())
    };

    if cli.link {
        if cli.input.is_empty() {
            eprintln!("linker requires at least one input object file");
            process::exit(1);
        }

        let mut objects = Vec::new();
        for path in &cli.input {
            let mut buf = Vec::new();
            File::open(path)?.read_to_end(&mut buf)?;
            objects.push(buf);
        }

        let instrs = link_objects(objects).unwrap();
        File::create(output)?.write_all(&instrs)?;
        return Ok(());
    }

    if cli.object {
        if cli.input.len() != 1 {
            eprintln!("assembler requires exactly one input file");
            process::exit(1);
        }

        let filename = &cli.input[0];
        let ext = filename.rsplit('.').next().unwrap_or("");

        let object_bytes = if ext == "masm" {
            // parse assembly file
            let mut asm_code = String::new();
            File::open(filename)?.read_to_string(&mut asm_code)?;
            let instrs: Vec<Instr> = parse_assembly(&asm_code).unwrap();
            assemble_object(&instrs).unwrap()
        } else {
            // treat as high-level source
            let mut code = String::new();
            File::open(filename)?.read_to_string(&mut code)?;
            let lexer = Lexer::new(&code);
            let ast = parser::Parser::new(lexer).parse().unwrap();
            let var_env = check_types(&ast).unwrap();
            check_semantics(&ast).unwrap();
            let instrs = gen_instrs(&ast, var_env).unwrap();
            assemble_object(&instrs).unwrap()
        };

        File::create(output)?.write_all(&object_bytes)?;
        return Ok(());
    }

    // default: compile source to binary
    if let Some(filename) = cli.input.get(0) {
        compile_file(filename, &output, cli.asm, cli.tokens, cli.ast)?;
        return Ok(());
    }

    // fallback: print help
    Cli::command().print_help().unwrap();
    println!();
    process::exit(1);
}
