#![allow(unused)]

use std::io;

use clap::{CommandFactory, Parser};
use mgcc::{compile_source, run_repl};

#[derive(Parser, Debug)]
#[command(author, version, about)]
struct Cli {
    #[arg(value_name = "file")]
    input: Vec<String>,

    #[arg(short, long)]
    repl: bool,

    #[arg(short = 'S', long)]
    asm: bool,

    #[arg(short = 't', long)]
    tokens: bool,

    #[arg(short = 'A', long)]
    ast: bool,

    #[arg(short, long)]
    output: Option<String>,

    #[arg(long)]
    lib: bool,
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
