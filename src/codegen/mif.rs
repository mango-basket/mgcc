use std::collections::HashMap;

use crate::{
    codegen::ir_builder::FunctionContext,
    grammar::ast::{TypedAstKind, TypedAstNode},
    semantic::type_check::Type,
};

fn type_to_mif(ty: &Type) -> String {
    match ty {
        Type::Unit => "void".to_string(),
        other => other.to_string(),
    }
}

pub fn gen_mif(
    ast: &TypedAstNode<'_>,
    funcs: &HashMap<String, FunctionContext>,
    module_name: &str,
) -> String {
    let mut out = String::new();

    out.push_str(&format!("module {}\n", module_name));
    out.push('\n');

    let exports = collect_exports(ast);

    for name in &exports {
        if let Some(ctx) = funcs.get(name) {
            let params_str: Vec<String> = ctx
                .param_names
                .iter()
                .zip(ctx.signature.params.iter())
                .map(|(pname, pty)| format!("{}: {}", pname, type_to_mif(pty)))
                .collect();
            let ret_str = type_to_mif(&ctx.signature.ret);
            out.push_str(&format!(
                "fn {}({}) -> {}\n",
                name,
                params_str.join(", "),
                ret_str
            ));
        }
    }

    out
}

fn collect_exports(ast: &TypedAstNode<'_>) -> Vec<String> {
    let mut exports = Vec::new();
    walk_for_exports(ast, &mut exports);
    exports
}

fn walk_for_exports(ast: &TypedAstNode<'_>, out: &mut Vec<String>) {
    match &ast.kind {
        TypedAstKind::Items(items) => {
            for item in items {
                walk_for_exports(item, out);
            }
        }
        TypedAstKind::Func {
            is_export,
            name,
            body,
        } => {
            if *is_export {
                out.push(name.span.get_str().to_string());
            }
            walk_for_exports(body, out);
        }
        TypedAstKind::Statements(stmts) => {
            for stmt in stmts {
                walk_for_exports(stmt, out);
            }
        }
        TypedAstKind::Module(_) => {}
        TypedAstKind::Use(_) => {}
        _ => {}
    }
}
