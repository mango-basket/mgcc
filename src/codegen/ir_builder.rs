use std::collections::HashMap;

use computils::instr::Instr;

// sp and fp registers
const SP: u8 = 8;
const FP: u8 = 9;

use crate::{
    error::{CompilerError, CompilerResult},
    grammar::ast::{TypedAstKind, TypedAstNode},
    semantic::type_check::{FnSignature, Type},
    tokenizer::token::{Span, Token, TokenKind},
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
    pub data_strings: HashMap<String, String>,
    pub data_counter: usize,
    pub label_counter: usize,
    pub loop_stack: Vec<(String, String)>, // (loop head, loop end)
    pub cur_func: Option<String>,
}

impl<'ip> Compiler {
    pub fn enter_function(&mut self, name: &str) -> CompilerResult<'ip, ()> {
        if self.functions.contains_key(name) {
            self.cur_func = Some(name.to_string());
            Ok(())
        } else {
            Err(CompilerError::Semantic {
                err: format!("attempted to enter undeclared function `{}`", name),
                span: Span::new(0, 0, ""),
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

    fn lookup_local_slot(&self, name: &str) -> Option<i8> {
        self.cur_func_ctx_ref()
            .symbols
            .get(name)
            .and_then(|(slot, _ty)| *slot)
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

    fn gen_branching(
        &mut self,
        cond: &'ip TypedAstNode<'ip>,
        lbl_true: String,
        lbl_false: String,
    ) -> CompilerResult<'ip, Vec<Instr>> {
        let mut instrs = Vec::new();

        match &cond.kind {
            TypedAstKind::BinaryOp { left, op, right } => {
                match op.kind {
                    TokenKind::And => {
                        // if its false jump straight to false
                        if left.kind.is_leaf() {
                            instrs.extend(self.gen_branching(
                                &left,
                                lbl_true.clone(),
                                lbl_false.clone(),
                            )?);
                        } else {
                            let mid = self.next_label();
                            instrs.extend(self.gen_branching(
                                &left,
                                mid.clone(),
                                lbl_false.clone(),
                            )?);
                            instrs.push(Instr::Lbl(mid));
                        }

                        instrs.extend(self.gen_branching(&right, lbl_true, lbl_false)?);
                    }

                    // if the first one is true jump striaght to true
                    TokenKind::Or => {
                        if left.kind.is_leaf() {
                            // if left is true, jump straight to true
                            instrs.extend(self.gen_branching(
                                &left,
                                lbl_true.clone(),
                                lbl_false.clone(),
                            )?);
                        } else {
                            let mid = self.next_label();
                            instrs.extend(self.gen_branching(
                                &left,
                                lbl_true.clone(),
                                mid.clone(),
                            )?);
                            instrs.push(Instr::Lbl(mid));
                        }

                        instrs.extend(self.gen_branching(&right, lbl_true, lbl_false)?);
                    }

                    // comparisons
                    TokenKind::Eq
                    | TokenKind::Neq
                    | TokenKind::Lt
                    | TokenKind::Gt
                    | TokenKind::Lte
                    | TokenKind::Gte => {
                        instrs.extend(self.gen_instrs(&left)?);
                        instrs.extend(self.gen_instrs(&right)?);
                        instrs.push(Instr::Cmp);

                        match op.kind {
                            TokenKind::Eq => instrs.push(Instr::JeqLbl(lbl_true)),
                            TokenKind::Neq => {
                                instrs.push(Instr::JeqLbl(lbl_false.clone()));
                                instrs.push(Instr::JmpLbl(lbl_true));
                            }
                            TokenKind::Lt => instrs.push(Instr::JltLbl(lbl_true)),
                            TokenKind::Gt => instrs.push(Instr::JgtLbl(lbl_true)),
                            TokenKind::Lte => {
                                instrs.push(Instr::JgtLbl(lbl_false.clone()));
                                instrs.push(Instr::JmpLbl(lbl_true));
                            }
                            TokenKind::Gte => {
                                instrs.push(Instr::JltLbl(lbl_false.clone()));
                                instrs.push(Instr::JmpLbl(lbl_true));
                            }
                            _ => unreachable!(),
                        }

                        instrs.push(Instr::JmpLbl(lbl_false));
                    }

                    _ => {
                        return Err(CompilerError::UnexpectedToken {
                            got: op.clone(),
                            expected: "logical or comparison operator",
                        });
                    }
                }
            }

            _ => {
                // fallback
                instrs.extend(self.gen_instrs(cond)?);
                instrs.push(Instr::Push(0));
                instrs.push(Instr::Cmp);
                instrs.push(Instr::JeqLbl(lbl_false.clone()));
                instrs.push(Instr::JmpLbl(lbl_true));
            }
        }

        Ok(instrs)
    }

    pub fn gen_instrs(&mut self, ast: &'ip TypedAstNode<'ip>) -> CompilerResult<'ip, Vec<Instr>> {
        let mut instrs = Vec::new();

        match &ast.kind {
            TypedAstKind::Int(kind) => {
                if let TokenKind::Int(num) = kind {
                    instrs.push(Instr::Push(*num))
                } else {
                    unreachable!()
                }
            }
            TypedAstKind::String(kind) => {
                if let TokenKind::String(_) = kind {
                    let name = format!("__str_{}", self.data_counter);
                    self.data_strings
                        .insert(name.clone(), ast.get_span().get_str().to_string());
                    instrs.push(Instr::Data(name));
                    self.data_counter += 1;
                } else {
                    unreachable!()
                }
            }
            TypedAstKind::Char(kind) => {
                if let TokenKind::Char(ch) = kind {
                    instrs.push(Instr::Push(*ch as u16))
                } else {
                    unreachable!()
                }
            }
            TypedAstKind::UnaryOp { op, operand } => {
                instrs.extend(self.gen_instrs(&operand)?);
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
            TypedAstKind::BinaryOp { left, op, right } => {
                let sub_instrs = self.gen_bin_op(&left, &op, &right)?;
                instrs.extend(sub_instrs)
            }
            TypedAstKind::Identifier(kind) => {
                if let TokenKind::Identifier(ref name) = kind {
                    if let Some(ofst) = self.lookup_local_slot(name) {
                        instrs.push(Instr::Ldr(FP, ofst));
                    } else {
                        return Err(CompilerError::UndefinedIdentifier(ast.get_span()));
                    }
                } else {
                    unreachable!();
                }
            }
            TypedAstKind::Bool(kind) => {
                if let TokenKind::Bool(bool) = kind {
                    instrs.push(Instr::Push(*bool as u16));
                } else {
                    unreachable!()
                }
            }
            TypedAstKind::VarDef { name, rhs } => {
                // locals are already allocated
                let slot = self
                    .lookup_local_slot(name.span.get_str())
                    .expect("unallocated local detected in codegen");

                instrs.extend(self.gen_instrs(&rhs)?);
                instrs.push(Instr::Str(FP, slot));
            }
            TypedAstKind::Statements(asts) => {
                for ast in asts {
                    instrs.extend(self.gen_instrs(&ast)?);
                }
            }
            TypedAstKind::Reassign { lhs, rhs } => match &lhs.kind {
                TypedAstKind::Identifier(ident_kind) => {
                    let ofst = if let TokenKind::Identifier(ref ident) = ident_kind {
                        if let Some(ofst) = self.lookup_local_slot(ident) {
                            ofst
                        } else {
                            return Err(CompilerError::UndefinedIdentifier(lhs.get_span()));
                        }
                    } else {
                        unreachable!()
                    };

                    instrs.extend(self.gen_instrs(&rhs)?);
                    instrs.push(Instr::Str(FP, ofst));
                }
                TypedAstKind::Deref(inner) => {
                    instrs.extend(self.gen_instrs(&rhs)?);
                    instrs.extend(self.gen_instrs(&inner)?);
                    instrs.push(Instr::Stw);
                }
                TypedAstKind::Index {
                    lhs: indexed,
                    rhs: idx,
                } => {
                    instrs.extend(self.gen_instrs(rhs)?);
                    instrs.extend(self.gen_instrs(indexed)?);
                    instrs.extend(self.gen_instrs(idx)?);
                    instrs.extend([
                        Instr::Push(lhs.eval_ty.get_size() as u16),
                        Instr::Mul,
                        Instr::Add,
                    ]);
                    if rhs.eval_ty.get_size() == 1 {
                        instrs.push(Instr::Stb);
                    } else {
                        instrs.push(Instr::Stw);
                    }
                }
                _ => {}
            },
            TypedAstKind::IfElse {
                condition,
                ifbody,
                elsebody,
            } => {
                let lbl_if = self.next_label();
                let lbl_else = self.next_label();
                let lbl_end = self.next_label();

                if elsebody.is_some() {
                    instrs.extend(self.gen_branching(
                        &condition,
                        lbl_if.clone(),
                        lbl_else.clone(),
                    )?);
                } else {
                    instrs.extend(self.gen_branching(
                        &condition,
                        lbl_if.clone(),
                        lbl_end.clone(),
                    )?);
                }

                // generate if-body
                instrs.push(Instr::Lbl(lbl_if));
                instrs.extend(self.gen_instrs(&ifbody)?);

                // after if-body, jump to end
                instrs.push(Instr::JmpLbl(lbl_end.clone()));

                // else-body
                if let Some(else_ast) = elsebody {
                    instrs.push(Instr::Lbl(lbl_else));
                    instrs.extend(self.gen_instrs(&else_ast)?);
                }

                // end label
                instrs.push(Instr::Lbl(lbl_end));
            }
            TypedAstKind::Loop(body) => {
                let head_lbl = self.next_label();
                let end_lbl = self.next_label();

                self.loop_stack.push((head_lbl.clone(), end_lbl.clone()));

                instrs.push(Instr::Lbl(head_lbl.clone()));
                instrs.extend(self.gen_instrs(&body)?);
                instrs.push(Instr::JmpLbl(head_lbl.clone()));
                instrs.push(Instr::Lbl(end_lbl.clone()));

                self.loop_stack.pop();
            }
            TypedAstKind::Continue => instrs.push(Instr::JmpLbl(
                self.loop_stack
                    .last()
                    .ok_or(
                        CompilerError::Semantic {
                            err: "continue found outside loop (unreachable)".into(),
                            span: ast.get_span(),
                        }, // Shouldnt ever happen because of the semantic analyzer
                    )?
                    .0
                    .clone(),
            )),
            TypedAstKind::Break(ref opt_expr) => {
                if let Some(expr) = opt_expr {
                    instrs.extend(self.gen_instrs(&expr)?);
                };

                instrs.push(Instr::JmpLbl(
                    self.loop_stack
                        .last()
                        .ok_or(
                            CompilerError::Semantic {
                                err: "break found outside loop (unreachable)".into(),
                                span: ast.get_span(),
                            }, // Shouldnt ever happen because of the semantic analyzer
                        )?
                        .1
                        .clone(),
                ));
            }
            TypedAstKind::Ref(inner) => {
                match inner.kind {
                    TypedAstKind::Identifier(ref ident_kind) => {
                        if let TokenKind::Identifier(ref name) = ident_kind {
                            if let Some(slot) = self.lookup_local_slot(name) {
                                instrs.push(Instr::Pushr(5)); // push fp onto stack
                                instrs.push(Instr::Push(slot as u16)); // push addr rel to fp
                                instrs.push(Instr::Push(2));
                                instrs.push(Instr::Mul);
                                instrs.push(Instr::Sub); // addr = fp - slot * 2
                            } else {
                                return Err(CompilerError::UndefinedIdentifier(inner.get_span()));
                            }
                        } else {
                            unreachable!();
                        }
                    }
                    TypedAstKind::Deref(ref inner) => instrs.extend(self.gen_instrs(&inner)?),
                    _ => unreachable!(),
                }
            }
            TypedAstKind::Deref(inner) => {
                instrs.extend(self.gen_instrs(&inner)?);
                instrs.push(Instr::Ldw);
            }
            TypedAstKind::Disp(printable) => {
                instrs.extend(self.gen_instrs(&printable)?);
                instrs.push(Instr::Popr(0));
                instrs.push(Instr::Int(0)) // prints r0
            }
            TypedAstKind::Items(asts) => {
                for ast in asts {
                    instrs.extend(self.gen_instrs(&ast)?);
                }
            }
            TypedAstKind::Func {
                name,
                params: _,
                body,
            } => {
                let fname = name.span.get_str().to_string();
                instrs.push(Instr::Lbl(fname.clone()));

                self.enter_function(&fname)
                    .expect("semantic run guarantees existence of function");

                // prologue
                instrs.extend([
                    Instr::Pushr(FP),   // save old FP
                    Instr::Mov(FP, SP), // set new FP = SP
                ]);

                // allocate locals
                // find biggest local offset
                let ofst = self.cur_func_ctx().fp_offset;
                instrs.extend([
                    Instr::Push((ofst as i16) as u16),
                    Instr::Pushr(FP),
                    Instr::Add,
                    Instr::Popr(SP),
                ]);

                // body
                instrs.extend(self.gen_instrs(&body)?);

                // default epilogue (in case no explicit return)
                instrs.extend([
                    Instr::Mov(SP, FP), // pop locals
                    Instr::Popr(FP),    // restore old FP
                    Instr::Ret,         // return
                ]);

                self.exit_function();
            }
            TypedAstKind::Return(expr_opt) => {
                if let Some(expr) = expr_opt {
                    instrs.extend(self.gen_instrs(&expr)?); // compute return value
                    instrs.push(Instr::Str(
                        FP,
                        self.lookup_local_slot("__return_addr").unwrap(),
                    ));
                    // store into return slot
                }

                // epilogue
                instrs.extend([Instr::Mov(SP, FP), Instr::Popr(FP), Instr::Ret]);
            }
            TypedAstKind::FuncCall { name, args } => {
                let sig = self
                    .functions
                    .get(name.span.get_str())
                    .map(|f| f.signature.clone())
                    .expect("call to undeclared function");

                // allocate hidden return slot if needed
                if sig.ret != Type::Unit {
                    instrs.push(Instr::Push(0));
                }

                // push args left to right
                for arg in args.iter() {
                    instrs.extend(self.gen_instrs(arg)?);
                }

                instrs.push(Instr::CallLbl(name.span.get_str().to_string()));

                // pop args (caller cleanup)
                let arg_count = args.len();
                if arg_count > 0 {
                    instrs.extend([
                        Instr::Pushr(SP),
                        Instr::Push(2),
                        Instr::Push(arg_count as u16),
                        Instr::Mul,
                        Instr::Add,
                        Instr::Popr(SP),
                    ]);
                }
            }
            TypedAstKind::As { lhs, rhs } => {
                instrs.extend(self.gen_instrs(lhs)?);

                match rhs.to_string().as_str() {
                    // if rhs is int, lhs is bool or char, both get reinterpretted
                    "int" => {} // do nothing

                    // if rhs is char, lhs has to be int
                    // mask the high bits out
                    "char" => {
                        instrs.extend([Instr::Push(0xFF), Instr::And]);
                    }
                    _ => unreachable!("type checker guarantees `as` coersions"),
                }
            }
            TypedAstKind::Index { lhs, rhs } => {
                // type checker guarantees that lhs is an array
                // lhs wil evaluate to an address
                instrs.extend(self.gen_instrs(lhs)?);

                // rhs will evaluate to an integer
                instrs.extend(self.gen_instrs(rhs)?);
                instrs.extend([Instr::Push(ast.eval_ty.get_size() as u16), Instr::Mul]);

                // add them and access memory at the address
                if ast.eval_ty.get_size() == 1 {
                    instrs.extend([Instr::Add, Instr::Ldb]);
                } else {
                    instrs.extend([Instr::Add, Instr::Ldw]);
                }
            }
            TypedAstKind::Array(items) => {
                // Allocate the array
                instrs.extend([
                    Instr::Pushr(SP),
                    Instr::Push(ast.eval_ty.get_padded_size() as u16),
                    Instr::Sub,
                    Instr::Popr(SP),
                ]);

                // Put pointer to beginning of array on top of the stack
                instrs.extend([Instr::Pushr(SP), Instr::Push(2), Instr::Add]);

                for (idx, item) in items.iter().enumerate() {
                    instrs.extend(self.gen_instrs(item)?);
                    instrs.extend([
                        // Duplicate the address
                        Instr::Ldr(SP, 4),
                        Instr::Push(idx as u16),
                        Instr::Push(item.eval_ty.get_size() as u16),
                        Instr::Mul,
                        Instr::Add,
                    ]);

                    if item.eval_ty.get_size() == 1 {
                        instrs.push(Instr::Stb);
                    } else {
                        instrs.push(Instr::Stw);
                    }
                }
            }
            TypedAstKind::ArrayDef { .. } => {
                // Allocate space and push pointer to beginning of array
                instrs.extend([
                    Instr::Pushr(SP),
                    Instr::Push(ast.eval_ty.get_padded_size() as u16),
                    Instr::Sub,
                    Instr::Popr(SP),
                    Instr::Pushr(SP),
                    Instr::Push(2),
                    Instr::Add,
                ]);
            }
        }

        Ok(instrs)
    }

    fn gen_bin_op(
        &mut self,
        left: &'ip TypedAstNode<'_>,
        op: &'ip Token<'_>,
        right: &'ip TypedAstNode<'_>,
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
            TokenKind::Mod => instrs.push(Instr::Mod),

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
