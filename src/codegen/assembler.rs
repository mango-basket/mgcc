use crate::{
    codegen::instr::Instr,
    error::{CompilerError, CompilerResult},
};

struct Symbol {
    name: String,
    val: u16,
}

struct Reloc {
    instr_idx: usize, // index in vec
    sym_name: String,
}

type Symbols = Vec<Symbol>;
type Relocs = Vec<Reloc>;

pub struct Object {
    instrs: Vec<Instr>,
    symbols: Symbols,
    relocs: Relocs,
}

pub fn assemble<'a>(instrs: Vec<Instr>) -> CompilerResult<'a, Object> {
    let mut symbols = Vec::new();
    let mut relocs = Vec::new();
    let mut byte_pos = 0u16;

    // first pass: record label positions
    for instr in &instrs {
        if let Instr::Lbl(ref name) = instr {
            symbols.push(Symbol {
                name: name.clone(),
                val: byte_pos,
            });
        } else {
            byte_pos += instr.byte_len() as u16;
        }
    }

    // second pass: track relocations
    let mut byte_pos = 0u16;
    let mut resolved_instrs = Vec::new();

    for instr in instrs {
        match instr {
            Instr::Lbl(_) => {} // labels don’t emit bytes

            Instr::JmpLbl(ref name)
            | Instr::JltLbl(ref name)
            | Instr::JgtLbl(ref name)
            | Instr::JeqLbl(ref name)
            | Instr::CallLbl(ref name) => {
                // check if symbol exists
                if let Some(sym) = symbols.iter().find(|s| &s.name == name) {
                    let rel = sym.val as i16 - (byte_pos as i16 + instr.byte_len() as i16);
                    let resolved = match instr {
                        Instr::JmpLbl(_) => Instr::Jmp(rel as i8),
                        Instr::JltLbl(_) => Instr::Jlt(rel as i8),
                        Instr::JgtLbl(_) => Instr::Jgt(rel as i8),
                        Instr::JeqLbl(_) => Instr::Jeq(rel as i8),
                        Instr::CallLbl(_) => Instr::Call(sym.val),
                        _ => unreachable!(),
                    };
                    byte_pos += resolved.byte_len() as u16;
                    resolved_instrs.push(resolved);
                } else {
                    // add to relocation table for linker
                    relocs.push(Reloc {
                        instr_idx: resolved_instrs.len(),
                        sym_name: name.clone(),
                    });
                    byte_pos += instr.byte_len() as u16;
                    resolved_instrs.push(instr);
                }
            }

            other => {
                byte_pos += other.byte_len() as u16;
                resolved_instrs.push(other);
            }
        }
    }

    Ok(Object {
        instrs: resolved_instrs,
        symbols,
        relocs,
    })
}

pub fn link_objects<'a>(objects: Vec<Object>) -> CompilerResult<'a, Vec<Instr>> {
    let mut linked_instrs = Vec::new();
    let mut linked_symbols = Vec::new();
    let mut obj_offsets = Vec::new();

    // merge symbols and calculate offsets
    let mut byte_pos = 0u16;
    for obj in &objects {
        obj_offsets.push(byte_pos);
        for sym in &obj.symbols {
            linked_symbols.push(Symbol {
                name: sym.name.clone(),
                val: sym.val + byte_pos,
            });
        }
        byte_pos += obj.instrs.iter().map(|i| i.byte_len() as u16).sum::<u16>();
    }

    // merge instructions
    for obj in &objects {
        linked_instrs.extend(obj.instrs.clone());
    }

    // patch relocations
    for (obj_idx, obj) in objects.iter().enumerate() {
        let base_offset = obj_offsets[obj_idx];
        for reloc in &obj.relocs {
            let instr_idx = reloc.instr_idx;
            let instr = &linked_instrs[instr_idx];

            if let Some(sym) = linked_symbols.iter().find(|s| s.name == reloc.sym_name) {
                let rel = sym.val as i16 - (instr_idx as i16 + instr.byte_len() as i16);
                linked_instrs[instr_idx] = match instr {
                    Instr::JmpLbl(_) => Instr::Jmp(rel as i8),
                    Instr::JltLbl(_) => Instr::Jlt(rel as i8),
                    Instr::JgtLbl(_) => Instr::Jgt(rel as i8),
                    Instr::JeqLbl(_) => Instr::Jeq(rel as i8),
                    Instr::CallLbl(_) => Instr::Call(sym.val),
                    _ => unreachable!(),
                };
            } else {
                return Err(CompilerError::LinkerError(format!(
                    "unknwon symbol {}",
                    reloc.sym_name
                )));
            }
        }
    }

    Ok(linked_instrs)
}
