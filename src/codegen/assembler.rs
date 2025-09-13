use crate::{
    codegen::instr::Instr,
    error::{CompilerError, CompilerResult},
};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum RelocType {
    Abs16 = 0,
    Rel8 = 1, // relative 8-bit displacement (e.g. jmp/jlt/jgt/jeq)
}

#[derive(Debug, Clone)]
pub struct Reloc {
    pub offset: u16,      // byte offset into emitted code where operand bytes start
    pub sym_name: String, // symbolic name to resolve at link time
    pub kind: RelocType,
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: String,
    pub val: u16,
}

type Symbols = Vec<Symbol>;
type Relocs = Vec<Reloc>;

pub struct Object {
    pub instrs: Vec<Instr>,
    pub symbols: Symbols,
    pub relocs: Relocs, // assembler-time relocations with byte offsets
}

const OBJ_FILE_VERSION: u16 = 1;

impl Object {
    /// Serialize object into binary:
    /// [ "MOBJ" (4) ][version u16][instr_bytes_len u16]
    /// [symtable_len u16][reloctable_len u16]
    /// [instr_bytes...][symtable...][reloctable...]
    ///
    /// symtable: repeated (name bytes, 0u8, u16 addr)
    /// reloctable: repeated (u16 offset, u16 sym_index, u8 kind)
    pub fn to_bin(&self) -> Vec<u8> {
        let mut out = Vec::new();

        // header: magic + version
        out.extend([b'M', b'O', b'B', b'J']);
        out.extend(OBJ_FILE_VERSION.to_le_bytes());

        // instructions bytes
        let instr_bytes = gen_bin(&self.instrs);
        out.extend((instr_bytes.len() as u16).to_le_bytes());

        // symtable bytes (name\0 + u16 addr)
        let mut symtab_bytes = Vec::new();
        for Symbol { name, val } in &self.symbols {
            symtab_bytes.extend(name.bytes());
            symtab_bytes.push(0u8);
            symtab_bytes.extend(val.to_le_bytes());
        }
        out.extend((symtab_bytes.len() as u16).to_le_bytes());

        // reloctable bytes: need to convert sym_name -> sym_index
        let mut reloctab_bytes = Vec::new();
        for Reloc {
            offset,
            sym_name,
            kind,
        } in &self.relocs
        {
            let sym_index = self
                .symbols
                .iter()
                .position(|s| s.name == *sym_name)
                .expect("symbol referenced in reloc missing from symbol table")
                as u16;
            reloctab_bytes.extend(offset.to_le_bytes());
            reloctab_bytes.extend(sym_index.to_le_bytes());
            reloctab_bytes.push(*kind as u8);
        }
        out.extend((reloctab_bytes.len() as u16).to_le_bytes());

        // payload
        out.extend(instr_bytes);
        out.extend(symtab_bytes);
        out.extend(reloctab_bytes);

        out
    }
}

// parse assembly text into symbolic instruction vector
pub fn parse_assembly<'a>(input: &str) -> CompilerResult<'a, Vec<Instr>> {
    let mut instrs = Vec::new();

    for (lineno, line) in input.lines().enumerate() {
        let line = line.trim();

        // skip blank lines and semicolon comments
        if line.is_empty() || line.starts_with(';') {
            continue;
        }

        // label definition
        if let Some(label) = line.strip_suffix(':') {
            instrs.push(Instr::Lbl(label.to_string()));
            continue;
        }

        let mut parts = line.split_whitespace();
        let mnemonic = parts.next().unwrap().to_lowercase();
        let operand = parts.next();

        let instr = match mnemonic.as_str() {
            // no-operand
            "halt" => Instr::Halt,
            "loadp" => Instr::Loadp,
            "storep" => Instr::Storep,
            "cmp" => Instr::Cmp,
            "ret" => Instr::Ret,

            // immediates
            "push" => {
                let val: u16 = operand
                    .ok_or_else(|| CompilerError::Assembler {
                        msg: "missing operand for push".into(),
                        line: Some(lineno + 1),
                    })?
                    .parse()
                    .map_err(|_| CompilerError::Assembler {
                        msg: "invalid operand for push".into(),
                        line: Some(lineno + 1),
                    })?;
                Instr::Push(val)
            }
            "load" => {
                let reg: u8 = operand
                    .ok_or_else(|| CompilerError::Assembler {
                        msg: "missing operand for load".into(),
                        line: Some(lineno + 1),
                    })?
                    .parse()
                    .map_err(|_| CompilerError::Assembler {
                        msg: "invalid operand for load".into(),
                        line: Some(lineno + 1),
                    })?;
                Instr::Load(reg)
            }
            "store" => {
                let reg: u8 = operand
                    .ok_or_else(|| CompilerError::Assembler {
                        msg: "missing operand for store".into(),
                        line: Some(lineno + 1),
                    })?
                    .parse()
                    .map_err(|_| CompilerError::Assembler {
                        msg: "invalid operand for store".into(),
                        line: Some(lineno + 1),
                    })?;
                Instr::Store(reg)
            }

            // control flow (label form)
            "jmp" => {
                let target = operand.ok_or_else(|| CompilerError::Assembler {
                    msg: "missing label for jmp".into(),
                    line: Some(lineno + 1),
                })?;
                Instr::JmpLbl(target.to_string())
            }
            "jlt" => {
                let target = operand.ok_or_else(|| CompilerError::Assembler {
                    msg: "missing label for jlt".into(),
                    line: Some(lineno + 1),
                })?;
                Instr::JltLbl(target.to_string())
            }
            "jgt" => {
                let target = operand.ok_or_else(|| CompilerError::Assembler {
                    msg: "missing label for jgt".into(),
                    line: Some(lineno + 1),
                })?;
                Instr::JgtLbl(target.to_string())
            }
            "jeq" => {
                let target = operand.ok_or_else(|| CompilerError::Assembler {
                    msg: "missing label for jeq".into(),
                    line: Some(lineno + 1),
                })?;
                Instr::JeqLbl(target.to_string())
            }
            "call" => {
                let target = operand.ok_or_else(|| CompilerError::Assembler {
                    msg: "missing label for call".into(),
                    line: Some(lineno + 1),
                })?;
                Instr::CallLbl(target.to_string())
            }

            _ => {
                return Err(CompilerError::Assembler {
                    msg: format!("unknown mnemonic `{}`", mnemonic),
                    line: Some(lineno + 1),
                })
            }
        };

        instrs.push(instr);
    }

    Ok(instrs)
}

pub fn gen_bin(instrs: &Vec<Instr>) -> Vec<u8> {
    let mut code = Vec::new();

    for instr in instrs {
        code.extend(match instr {
            // Stack and control
            Instr::Push(val) => vec![0x01, (val & 0xFF) as u8, (val >> 8) as u8], // LE
            Instr::Halt => vec![0x0F],

            // Memory
            Instr::Load(addr) => vec![0x10, *addr],
            Instr::Store(addr) => vec![0x11, *addr],
            Instr::Loadp => vec![0x12],
            Instr::Storep => vec![0x13],

            // Jumps and Branches
            Instr::Jmp(displ) => vec![0x20, (*displ as u8)],
            Instr::Jlt(displ) => vec![0x21, (*displ as u8)],
            Instr::Jgt(displ) => vec![0x22, (*displ as u8)],
            Instr::Jeq(displ) => vec![0x23, (*displ as u8)],
            Instr::Call(addr) => vec![0x24, (*addr & 0xFF) as u8, (*addr >> 8) as u8],
            Instr::Ret => vec![0x25],

            // Integer Arithmetic
            Instr::Add => vec![0x30],
            Instr::Sub => vec![0x31],
            Instr::Mul => vec![0x32],
            Instr::Div => vec![0x33],
            Instr::Neg => vec![0x34],
            Instr::Cmp => vec![0x35],

            // Bitwise Ops
            Instr::Not => vec![0x40],
            Instr::And => vec![0x41],
            Instr::Or => vec![0x42],
            Instr::Xor => vec![0x43],
            Instr::Shft => vec![0x44],

            // Register operations
            Instr::Mov(rd, rs) => vec![0x50, (rd << 4) | rs],
            Instr::Pushr(rs) => vec![0x51, *rs],
            Instr::Popr(rd) => vec![0x52, *rd],

            // Video
            Instr::Print => vec![0x60],
            Instr::MvCur(ofst) => vec![0x61, *ofst as u8],

            // Label/symbolic forms should not reach gen_bin as-is; if they do,
            // it means assemble_object didn't finalize them. panic to make it obvious.
            Instr::Lbl(_)
            | Instr::CallLbl(_)
            | Instr::JmpLbl(_)
            | Instr::JltLbl(_)
            | Instr::JgtLbl(_)
            | Instr::JeqLbl(_) => {
                panic!("gen_bin called on unresolved symbolic instruction")
            }
        });
    }

    code
}

pub fn assemble_object(instrs: &Vec<Instr>) -> CompilerResult<Vec<u8>> {
    let mut out_instr = Vec::new();
    let mut byte_pos: u16 = 0;
    let mut symbols = HashMap::new();
    let mut relocs = Vec::new();

    for instr in instrs {
        match instr {
            Instr::Lbl(name) => {
                if let Some(_) = symbols.insert(name, byte_pos) {
                    return Err(CompilerError::Assembler {
                        msg: format!("symbol {} is defined multiple times", name),
                        line: None,
                    });
                }
            }

            Instr::JmpLbl(name)
            | Instr::JltLbl(name)
            | Instr::JgtLbl(name)
            | Instr::JeqLbl(name) => {
                let target_addr = match symbols.get(name) {
                    // Back reference
                    Some(addr) => (*addr as isize - byte_pos as isize) as i8,
                    // Forward reference
                    None => {
                        symbols.insert(name, 0xFFFF);
                        relocs.push(Reloc {
                            offset: byte_pos + 1,
                            sym_name: name.to_string(),
                            kind: RelocType::Rel8,
                        });
                        -1 // 0xFF
                    }
                };

                let unlabelled = match instr {
                    Instr::JmpLbl(_) => Instr::Jmp(target_addr),
                    Instr::JltLbl(_) => Instr::Jlt(target_addr),
                    Instr::JgtLbl(_) => Instr::Jgt(target_addr),
                    Instr::JeqLbl(_) => Instr::Jeq(target_addr),
                    _ => unreachable!(),
                };

                out_instr.push(unlabelled);
            }

            Instr::CallLbl(name) => {
                let target_addr = match symbols.get(name) {
                    Some(addr) => addr,
                    None => {
                        symbols.insert(name, 0xFFFF);
                        relocs.push(Reloc {
                            offset: byte_pos + 1,
                            sym_name: name.to_string(),
                            kind: RelocType::Abs16,
                        });
                        &0xFFFF
                    }
                };

                out_instr.push(Instr::Call(*target_addr));
            }

            concrete => out_instr.push(concrete.clone()),
        }
        byte_pos += instr.byte_len() as u16;
    }

    Ok(Object {
        instrs: out_instr,
        symbols: symbols
            .iter()
            .map(|(name, val)| Symbol {
                name: name.to_string(),
                val: *val,
            })
            .collect(),
        relocs: relocs,
    }
    .to_bin())
}
