use std::collections::HashMap;

use computils::instr::Instr;

// sp and fp registers
const SP: u8 = 4;
const FP: u8 = 5;

use crate::{
    error::{CompilerError, CompilerResult},
    grammar::ast::Ast,
    semantic::type_check::{FnSignature, Type},
    tokenizer::token::{Slice, Token, TokenKind},
};

type SymbolTable = HashMap<String, (Option<i8>, Type)>;

#[derive(Debug)]
pub struct FunctionContext {
    pub symbols: SymbolTable,
    pub fp_offset: i8,
    pub signature: FnSignature,
}

pub struct Compiler {
    pub functions: HashMap<String, FunctionContext>,
    pub label_counter: usize,
    pub loop_stack: Vec<(String, String)>, // (loop head, loop end)
    pub cur_func: Option<String>,
}

impl<'ip> Compiler {
    pub fn enter_function(&mut self, name: &str) -> CompilerResult<()> {
        if self.functions.contains_key(name) {
            self.cur_func = Some(name.to_string());
            Ok(())
        } else {
            Err(CompilerError::Semantic {
                err: format!("attempted to enter undeclared function `{}`", name),
                slice: Slice::new(0, 0, ""),
            })
        }
    }

    pub fn exit_function(&mut self) {
        self.cur_func = None;
    }

    fn cur_func_ctx(&mut self) -> &mut FunctionContext {
        let fname = self.cur_func.clone().expect("no current function");
        self.functions
            .get_mut(&fname)
            .expect("current function missing from map")
    }

    fn cur_func_ctx_ref(&self) -> &FunctionContext {
        let fname = self.cur_func.clone().expect("no current function");
        self.functions
            .get(&fname)
            .expect("current function missing from map")
    }

    fn alloc_local(&mut self, name: &str, ty: Type) -> i8 {
        let func = self.cur_func_ctx();
        let fp_offset = func.fp_offset;
        func.symbols.insert(name.to_string(), (Some(fp_offset), ty));
        func.fp_offset -= 2;
        fp_offset
    }

    fn lookup_local_slot(&self, name: &str) -> Option<i8> {
        self.cur_func_ctx_ref()
            .symbols
            .get(name)
            .and_then(|(slot, _ty)| *slot)
    }

    fn lookup_local_type(&self, name: &str) -> Option<Type> {
        self.cur_func_ctx_ref()
            .symbols
            .get(name)
            .map(|(_slot, ty)| ty.clone())
    }

    fn has_local(&self, name: &str) -> bool {
        self.cur_func_ctx_ref().symbols.contains_key(name)
    }

    fn next_label(&mut self) -> String {
        let id = self.label_counter;
        self.label_counter += 1;
        format!("L{}", id)
    }

    fn gen_comparison(&mut self, op: &TokenKind) -> Vec<Instr> {
        let mut instrs = Vec::new();
        let lbl_true = self.next_label();
        let lbl_end = self.next_label();

        // compare left - right
        instrs.push(Instr::Cmp);

        match op {
            TokenKind::Eq => {
                instrs.push(Instr::JeqLbl(lbl_true.clone())); // equal -> true
            }
            TokenKind::Neq => {
                // not equal -> jump to true if NOT zero
                // easiest: jump if equal -> skip true
                instrs.push(Instr::JeqLbl(lbl_end.clone()));
                instrs.push(Instr::JmpLbl(lbl_true.clone()));
            }
            TokenKind::Lt => {
                instrs.push(Instr::JltLbl(lbl_true.clone())); // < -> true
            }
            TokenKind::Gt => {
                instrs.push(Instr::JgtLbl(lbl_true.clone())); // > -> true
            }
            TokenKind::Lte => {
                // <= means not (>)
                instrs.push(Instr::JgtLbl(lbl_end.clone())); // if >, skip true
                instrs.push(Instr::JmpLbl(lbl_true.clone()));
            }
            TokenKind::Gte => {
                // >= means not (<)
                instrs.push(Instr::JltLbl(lbl_end.clone())); // if <, skip true
                instrs.push(Instr::JmpLbl(lbl_true.clone()));
            }
            _ => unreachable!(),
        }

        // false branch
        instrs.push(Instr::Push(0));
        instrs.push(Instr::JmpLbl(lbl_end.clone()));

        // true branch
        instrs.push(Instr::Lbl(lbl_true));
        instrs.push(Instr::Push(1));

        // end
        instrs.push(Instr::Lbl(lbl_end));

        instrs
    }

    pub fn gen_instrs(&mut self, ast: &'ip Ast<'ip>) -> CompilerResult<'ip, Vec<Instr>> {
        let mut instrs = Vec::new();

        match ast {
            Ast::Int(tok) => {
                if let TokenKind::Int(num) = tok.kind {
                    instrs.push(Instr::Push(num))
                } else {
                    unreachable!()
                }
            }
            Ast::UnaryOp { op, operand } => {
                instrs.extend(self.gen_instrs(operand)?);
                match op.kind {
                    TokenKind::Plus => {}
                    TokenKind::Minus => instrs.push(Instr::Neg),
                    TokenKind::Bnot => instrs.push(Instr::Not),
                    TokenKind::Not => instrs.extend([Instr::Push(0), Instr::Cmp]),
                    _ => {
                        return Err(CompilerError::UnexpectedToken {
                            got: op.clone(),
                            expected: "-' or '+",
                        })
                    }
                }
            }
            Ast::BinaryOp { left, op, right } => instrs.extend(self.gen_bin_op(left, op, right)?),
            Ast::Identifier(token) => {
                if let TokenKind::Identifier(ref name) = token.kind {
                    if let Some(ofst) = self.lookup_local_slot(name) {
                        instrs.push(Instr::Loadr(FP, ofst));
                    } else {
                        return Err(CompilerError::UndefinedIdentifier(token.clone()));
                    }
                } else {
                    unreachable!();
                }
            }
            Ast::Bool(token) => {
                if let TokenKind::Bool(bool) = token.kind {
                    instrs.push(Instr::Push(bool as u16));
                } else {
                    unreachable!()
                }
            }
            Ast::VarDef {
                name,
                vartype: _,
                rhs,
            } => {
                // look up type from var_env (guaranteed by typechecker)
                let ty = self
                    .lookup_local_type(name.slice.get_str())
                    .expect("typechecker ensures variables exist");

                let slot = self.alloc_local(name.slice.get_str(), ty);

                instrs.extend(self.gen_instrs(rhs)?);
                instrs.push(Instr::Storer(FP, slot));
            }
            Ast::Statements(asts) => {
                for ast in asts {
                    instrs.extend(self.gen_instrs(ast)?);
                }
            }
            Ast::Reassign { lhs, rhs } => match &**lhs {
                Ast::Identifier(ident_tok) => {
                    let ofst = if let TokenKind::Identifier(ref ident) = ident_tok.kind {
                        if let Some(ofst) = self.lookup_local_slot(ident) {
                            ofst
                        } else {
                            return Err(CompilerError::UndefinedIdentifier(ident_tok.clone()));
                        }
                    } else {
                        unreachable!()
                    };

                    instrs.extend(self.gen_instrs(rhs)?);
                    instrs.push(Instr::Storer(FP, ofst));
                }
                Ast::Deref(inner) => {
                    instrs.extend(self.gen_instrs(inner)?);
                    instrs.extend(self.gen_instrs(rhs)?);
                    instrs.push(Instr::Storep);
                }
                _ => {}
            },
            Ast::IfElse {
                condition,
                ifbody,
                elsebody,
            } => {
                // generate code for condition
                instrs.extend(self.gen_instrs(condition)?);

                let lbl_else = self.next_label();
                let lbl_end = self.next_label();

                // jump to else if condition is false (0)
                instrs.extend([Instr::Push(0), Instr::Cmp, Instr::JeqLbl(lbl_else.clone())]); // assuming 0 = false, 1 = true

                // generate if-body
                instrs.extend(self.gen_instrs(ifbody)?);

                // after if-body, jump to end
                instrs.push(Instr::JmpLbl(lbl_end.clone()));

                // else-body
                instrs.push(Instr::Lbl(lbl_else));
                if let Some(else_ast) = elsebody {
                    instrs.extend(self.gen_instrs(else_ast)?);
                }

                // end label
                instrs.push(Instr::Lbl(lbl_end));
            }
            Ast::Loop(body) => {
                let head_lbl = self.next_label();
                let end_lbl = self.next_label();

                self.loop_stack.push((head_lbl.clone(), end_lbl.clone()));

                instrs.push(Instr::Lbl(head_lbl.clone()));
                instrs.extend(self.gen_instrs(body)?);
                instrs.extend([Instr::JmpLbl(head_lbl.clone()), Instr::Lbl(end_lbl.clone())]);

                self.loop_stack.pop();
            }
            Ast::Continue => instrs.push(Instr::JmpLbl(
                self.loop_stack
                    .last()
                    .ok_or(
                        CompilerError::Semantic {
                            err: "continue found outside loop (unreachable)".into(),
                            slice: ast.get_slice(),
                        }, // Shouldnt ever happen because of the semantic analyzer
                    )?
                    .0
                    .clone(),
            )),
            Ast::Break(ref opt_expr) => {
                if let Some(expr) = opt_expr {
                    instrs.extend(self.gen_instrs(expr)?);
                };

                instrs.push(Instr::JmpLbl(
                    self.loop_stack
                        .last()
                        .ok_or(
                            CompilerError::Semantic {
                                err: "break found outside loop (unreachable)".into(),
                                slice: ast.get_slice(),
                            }, // Shouldnt ever happen because of the semantic analyzer
                        )?
                        .1
                        .clone(),
                ));
            }
            Ast::Ref(inner) => {
                match **inner {
                    Ast::Identifier(ref ident_tok) => {
                        if let TokenKind::Identifier(ref name) = ident_tok.kind {
                            if let Some(slot) = self.lookup_local_slot(name) {
                                instrs.push(Instr::Pushr(5)); // push fp onto stack
                                instrs.push(Instr::Push(slot as u16)); // push addr rel to fp
                                instrs.push(Instr::Push(2));
                                instrs.push(Instr::Mul);
                                instrs.push(Instr::Sub); // addr = fp - slot * 2
                            } else {
                                return Err(CompilerError::UndefinedIdentifier(ident_tok.clone()));
                            }
                        } else {
                            unreachable!();
                        }
                    }
                    Ast::Deref(ref inner) => instrs.extend(self.gen_instrs(inner)?),
                    _ => unreachable!(),
                }
            }
            Ast::Deref(inner) => {
                instrs.extend(self.gen_instrs(inner)?);
                instrs.push(Instr::Loadp);
            }
            Ast::Disp(printable) => {
                instrs.extend(self.gen_instrs(printable)?);
                instrs.push(Instr::Popr(0));
                instrs.push(Instr::CallLbl("print".into())) // prints r0
            }
            Ast::Items(asts) => {
                for ast in asts {
                    instrs.extend(self.gen_instrs(ast)?);
                }
            }
            Ast::Func {
                name,
                params,
                body,
                ret,
            } => {
                let fname = name.slice.get_str().to_string();
                instrs.push(Instr::Lbl(fname.clone()));

                self.enter_function(&fname)
                    .expect("semantic run guarantees existence of function");

                // prologue
                instrs.extend([
                    Instr::Pushr(FP),   // save old FP
                    Instr::Mov(FP, SP), // set new FP = SP
                ]);

                // body
                instrs.extend(self.gen_instrs(body)?);

                // default epilogue (in case no explicit return)
                instrs.extend([
                    Instr::Mov(SP, FP), // pop locals
                    Instr::Popr(FP),    // restore old FP
                    Instr::Ret,         // return
                ]);

                self.exit_function();
            }
            Ast::Return(expr_opt) => {
                if let Some(expr) = expr_opt {
                    instrs.extend(self.gen_instrs(expr)?); // compute return value
                    instrs.push(Instr::Storer(FP, 2)); // store into return slot
                }

                // epilogue
                instrs.extend([Instr::Mov(SP, FP), Instr::Popr(FP), Instr::Ret]);
            }
            Ast::FuncCall { name, args } => {
                let sig = self
                    .functions
                    .get(name.slice.get_str())
                    .map(|f| f.signature.clone())
                    .expect("call to undeclared function");

                // allocate hidden return slot if needed
                if sig.ret != Type::Unit {
                    instrs.push(Instr::Push(0));
                }

                // push args right-to-left
                for arg in args.iter().rev() {
                    instrs.extend(self.gen_instrs(arg)?);
                }

                instrs.push(Instr::CallLbl(name.slice.get_str().to_string()));

                // pop args (caller cleanup)
                for _ in args {
                    instrs.push(Instr::Popr(0));
                }

                // fetch return value (if not unit)
                if sig.ret != Type::Unit {
                    instrs.push(Instr::Popr(0)); // move return into r0 (or just leave on stack if you want)
                    instrs.push(Instr::Pushr(0));
                }
            }
        }

        Ok(instrs)
    }

    fn gen_bin_op(
        &mut self,
        left: &'ip Box<Ast<'_>>,
        op: &'ip Token<'_>,
        right: &'ip Box<Ast<'_>>,
    ) -> Result<Vec<Instr>, CompilerError<'ip>> {
        let mut instrs = Vec::new();

        instrs.extend(self.gen_instrs(left)?);
        instrs.extend(self.gen_instrs(right)?);
        match op.kind {
            // Arithmetic
            TokenKind::Plus => instrs.push(Instr::Add),
            TokenKind::Minus => instrs.push(Instr::Sub),
            TokenKind::Star => instrs.push(Instr::Mul),
            TokenKind::Slash => instrs.push(Instr::Div),
            TokenKind::Mod => instrs.extend([
                Instr::Popr(1),
                Instr::Popr(0),
                Instr::Pushr(0),
                Instr::Pushr(0),
                Instr::Pushr(1),
                Instr::Div,
                Instr::Pushr(1),
                Instr::Mul,
                Instr::Sub,
            ]),

            // Comparison
            TokenKind::Eq
            | TokenKind::Neq
            | TokenKind::Lt
            | TokenKind::Gt
            | TokenKind::Lte
            | TokenKind::Gte => instrs.extend(self.gen_comparison(&op.kind)),

            // Logical + bitwisw
            TokenKind::And | TokenKind::Band => instrs.push(Instr::And),
            TokenKind::Or | TokenKind::Bor => instrs.push(Instr::Or),
            TokenKind::Xor => instrs.push(Instr::Xor),
            TokenKind::Shl => instrs.extend([Instr::Neg, Instr::Shft]),
            TokenKind::Shr => instrs.push(Instr::Shft),

            _ => {
                return Err(CompilerError::UnexpectedToken {
                    got: op.clone(),
                    expected: "+', '-', '*' or '/",
                })
            }
        }

        Ok(instrs)
    }
}
