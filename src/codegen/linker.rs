use crate::{
    codegen::{
        assembler::{Object, Symbol},
        instr::Instr,
    },
    error::{CompilerError, CompilerResult},
};

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
    for obj in objects.iter() {
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
                return Err(CompilerError::Linker(format!(
                    "unknwon symbol {}",
                    reloc.sym_name
                )));
            }
        }
    }

    Ok(linked_instrs)
}
