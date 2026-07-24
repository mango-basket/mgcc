#![allow(unused)]

pub mod codegen;
pub mod error;
pub mod grammar;
pub mod optimizer;
pub mod semantic;
pub mod tokenizer;

use std::io::{self, stdin, stdout, Write};

use tokenizer::lexer::Lexer;

use crate::{
    codegen::{
        backend::{gen_asm, gen_instrs},
        mif::gen_mif,
    },
    grammar::{
        ast::{TypedAstKind, TypedAstNode},
        parser,
    },
    optimizer::fold,
    semantic::{analyzer::check_semantics, type_check::check_types},
};

pub fn extract_module_name(ast: &TypedAstNode<'_>) -> Option<String> {
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

pub fn compile_source(
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

    let (typed_ast, funcs) = check_types(&ast).map_err(|e| e.to_string())?;
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

pub fn run_repl(dump_tokens: bool, dump_ast: bool) -> io::Result<()> {
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
