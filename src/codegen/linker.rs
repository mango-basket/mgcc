use std::collections::HashMap;

use crate::error::{CompilerError, CompilerResult};

const OBJ_FILE_VERSION: u16 = 1;
const VERSION_OFST: usize = 4;
const INSTR_LEN_OFST: usize = 7;
const SYM_LEN_OFST: usize = 9;
const RELOC_LEN_OFST: usize = 11;
const INSTR_BEGIN_OFST: usize = 13;

fn read_u16(object: &Vec<u8>, idx: usize) -> u16 {
    object[idx] as u16 | ((object[idx + 1] as u16) << 8)
}

pub fn link_objects<'a>(objects: Vec<Vec<u8>>) -> CompilerResult<'a, Vec<u8>> {
    let mut instrs: Vec<u8> = b"MBIN".iter().map(|&x| x).collect();
    let mut symbols = HashMap::new();
    let mut relocs = Vec::new();

    // set up symbols
    let mut obj_ofst = 0;
    let mut sym_ofst = 0;
    for object in objects {
        let mut obj_symbols = Vec::new();

        let magic = &object[0..VERSION_OFST];
        if magic != *b"MOBJ" {
            return Err(CompilerError::Linker(
                "not a valid object file (magic number not found)".to_string(),
            ));
        }

        let version = read_u16(&object, VERSION_OFST);
        if version != OBJ_FILE_VERSION {
            return Err(CompilerError::Linker(format!(
                "object file version ({}) does not match supported version ({})",
                version, OBJ_FILE_VERSION
            )));
        }

        let instr_len = read_u16(&object, INSTR_LEN_OFST);
        let sym_len = read_u16(&object, SYM_LEN_OFST);
        let reloc_len = read_u16(&object, RELOC_LEN_OFST);
        instrs.extend_from_slice(&object[INSTR_BEGIN_OFST..INSTR_BEGIN_OFST + instr_len as usize]);

        // set up symbol table
        let mut ofst = 0;
        let cur = |ofst| INSTR_BEGIN_OFST + instr_len as usize + ofst;
        while ofst < sym_len as usize {
            let mut name = String::new();
            while object[cur(ofst)] != 0 {
                name.push(object[cur(ofst)] as char);
                ofst += 1;
            }
            ofst += 1; // skip \0

            let mut addr = read_u16(&object, cur(ofst));
            // Resolved
            if addr != 0xFFFF {
                addr += obj_ofst;
            }

            ofst += 2; // skip addr

            obj_symbols.push((name, addr));
        }

        // set up relocs table
        ofst = 0;
        let cur = |ofst| INSTR_BEGIN_OFST + instr_len as usize + sym_len as usize + ofst;
        while ofst < reloc_len as usize {
            let instr_ofst = read_u16(&object, cur(ofst));
            ofst += 2;

            let sym_idx = read_u16(&object, cur(ofst));
            let sym_idx = sym_idx as usize + sym_ofst;
            ofst += 2;

            let kind = object[cur(ofst)];
            ofst += 1;

            relocs.push((instr_ofst, obj_symbols[sym_idx].0.clone(), kind));
        }

        // update global symbol table
        for (name, addr) in obj_symbols {
            symbols.insert(name, addr);
        }

        sym_ofst = symbols.len();
        obj_ofst += instr_len;
    }

    for (ofst, sym_name, kind) in relocs {
        let addr = match symbols.get(&sym_name) {
            Some(addr) => addr,
            None => {
                return Err(CompilerError::Linker(format!(
                    "symbol {sym_name} not found"
                )))
            }
        };

        // unresolved symbol
        if *addr == 0xFFFF {
            return Err(CompilerError::Linker(format!(
                "unresolved symbol {sym_name}"
            )));
        }

        // relative
        if kind == 1 {
            let rel = (*addr as isize - ofst as isize + 1) as i8;
            instrs[ofst as usize] = rel as u8;
        } else {
            let addr_bytes = addr.to_le_bytes();
            instrs[ofst as usize] = addr_bytes[0];
            instrs[ofst as usize + 1] = addr_bytes[1];
        }
    }

    Ok(instrs)
}
