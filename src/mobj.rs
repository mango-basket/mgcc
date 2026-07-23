use std::{
    collections::HashMap,
    fs,
    io::{self, Read},
    path::{Path, PathBuf},
};

use crate::{
    codegen::ir_builder::FunctionContext,
    semantic::type_check::{FnSignature, Type},
};

#[derive(Debug)]
pub struct Export {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret: Type,
}

#[derive(Debug)]
pub struct Metadata {
    pub module_name: String,
    pub dependencies: Vec<String>,
    pub exports: Vec<Export>,
}

impl Metadata {
    pub fn from_mobj<P: AsRef<Path>>(path: P) -> Result<Self, String> {
        let mut file = fs::File::open(&path)
            .map_err(|e| format!("could not open MOBJ file {}: {}", path.as_ref().display(), e))?;

        let mut header = [0u8; 16];
        file.read_exact(&mut header)
            .map_err(|e| format!("failed to read MOBJ header: {}", e))?;

        if &header[0..4] != b"MOBJ" {
            return Err("not a valid MOBJ file (bad magic)".to_string());
        }

        let version = u16::from_le_bytes([header[4], header[5]]);
        if version < 3 {
            return Err("MOBJ version too old, requires version 3+ for metadata".to_string());
        }

        let instr_bytes_len = u16::from_le_bytes([header[6], header[7]]) as usize;
        let data_bytes_len = u16::from_le_bytes([header[8], header[9]]) as usize;
        let symtable_len = u16::from_le_bytes([header[10], header[11]]) as usize;
        let reloctable_len = u16::from_le_bytes([header[12], header[13]]) as usize;
        let meta_len = u16::from_le_bytes([header[14], header[15]]) as usize;

        if meta_len == 0 {
            return Err("MOBJ file has no metadata section".to_string());
        }

        let meta_start = 16 + instr_bytes_len + data_bytes_len + symtable_len + reloctable_len;
        
        let mut file = fs::File::open(&path)
            .map_err(|e| format!("could not open MOBJ file: {}", e))?;
        file.seek(io::SeekFrom::Start(meta_start as u64))
            .map_err(|e| format!("failed to seek to metadata: {}", e))?;

        let mut meta_data = vec![0u8; meta_len];
        file.read_exact(&mut meta_data)
            .map_err(|e| format!("failed to read metadata: {}", e))?;

        Self::parse_metadata(&meta_data)
    }

    fn parse_metadata(data: &[u8]) -> Result<Self, String> {
        if data.len() < 8 {
            return Err("metadata section too small".to_string());
        }

        let read_u16 = |offset: usize| -> u16 {
            u16::from_le_bytes([data[offset], data[offset + 1]])
        };

        let name_ofst = read_u16(0);
        let dependency_count = read_u16(2) as usize;
        let export_count = read_u16(4) as usize;
        let param_count = read_u16(6) as usize;

        let mut pos = 8;
        let mut dependency_table = Vec::new();
        for _ in 0..dependency_count {
            dependency_table.push(read_u16(pos));
            pos += 2;
        }

        let mut export_table = Vec::new();
        for _ in 0..export_count {
            export_table.push(ExportEntry {
                name_ofst: read_u16(pos),
                ret_ofst: read_u16(pos + 2),
                first_param: read_u16(pos + 4),
                param_count: read_u16(pos + 6),
            });
            pos += 8;
        }

        let mut param_table = Vec::new();
        for _ in 0..param_count {
            param_table.push(ParamEntry {
                name_ofst: read_u16(pos),
                type_ofst: read_u16(pos + 2),
            });
            pos += 4;
        }

        let string_pool = StringPool::from_bytes(&data[pos..]);

        let module_name = string_pool.resolve(name_ofst).to_string();
        
        let dependencies = dependency_table
            .iter()
            .map(|&ofst| string_pool.resolve(ofst).to_string())
            .collect();

        let exports = export_table
            .into_iter()
            .map(|e| {
                let name = string_pool.resolve(e.name_ofst).to_string();
                let ret = string_pool.resolve(e.ret_ofst).to_string();
                
                let mut params = Vec::new();
                for i in 0..e.param_count as usize {
                    let idx = e.first_param as usize + i;
                    let pname = string_pool.resolve(param_table[idx].name_ofst).to_string();
                    let ptype = string_pool.resolve(param_table[idx].type_ofst).to_string();
                    params.push((pname, parse_type(&ptype)));
                }

                Export {
                    name,
                    params,
                    ret: parse_type(&ret),
                }
            })
            .collect();

        Ok(Metadata {
            module_name,
            dependencies,
            exports,
        })
    }
}

#[derive(Debug)]
struct ExportEntry {
    name_ofst: u16,
    ret_ofst: u16,
    first_param: u16,
    param_count: u16,
}

#[derive(Debug)]
struct ParamEntry {
    name_ofst: u16,
    type_ofst: u16,
}

struct StringPool {
    strings: Vec<String>,
    offsets: HashMap<u16, usize>,
}

impl StringPool {
    fn from_bytes(data: &[u8]) -> Self {
        let mut strings = Vec::new();
        let mut offsets = HashMap::new();
        let mut start = 0;

        for (i, &b) in data.iter().enumerate() {
            if b == 0 {
                if let Ok(s) = String::from_utf8(data[start..i].to_vec()) {
                    let offset = start as u16;
                    offsets.insert(offset, strings.len());
                    strings.push(s);
                }
                start = i + 1;
            }
        }

        StringPool { strings, offsets }
    }

    fn resolve(&self, offset: u16) -> &str {
        self.offsets
            .get(&offset)
            .map(|&idx| self.strings[idx].as_str())
            .unwrap_or("")
    }
}

fn parse_type(s: &str) -> Type {
    match s {
        "int" => Type::Int,
        "bool" => Type::Bool,
        "void" | "unit" => Type::Unit,
        "char" => Type::Char,
        s if s.starts_with("ref ") => Type::Ref(Box::new(parse_type(&s[4..]))),
        s if s.contains("->") => {
            let (head, ret) = s.split_once("->").unwrap();
            let ret = parse_type(ret.trim());
            let params_str = head.trim().trim_start_matches("fn").trim();
            let params = if params_str.starts_with('(') && params_str.ends_with(')') {
                &params_str[1..params_str.len()-1]
            } else {
                params_str
            };
            let param_types = if params.trim().is_empty() {
                Vec::new()
            } else {
                params.split(',')
                    .map(|p| p.trim().split_once(':').unwrap().1.trim())
                    .map(parse_type)
                    .collect()
            };
            Type::Fn { params: param_types, ret: Box::new(ret) }
        }
        _ => Type::Int, // fallback
    }
}

/// Search for a .mobj file in MANGO_PATHS environment variable and current directory
pub fn find_mobj_file(module_name: &str) -> Result<PathBuf, String> {
    let mut search_paths = Vec::new();

    // Add current working directory first (highest priority)
    if let Ok(cwd) = std::env::current_dir() {
        search_paths.push(cwd);
    }

    // Add MANGO_PATHS
    if let Ok(paths) = std::env::var("MANGO_PATHS") {
        for path in paths.split(':') {
            if !path.is_empty() {
                search_paths.push(PathBuf::from(path));
            }
        }
    }

    for path in search_paths {
        let candidate = path.join(format!("{}.mobj", module_name));
        if candidate.exists() {
            return Ok(candidate);
        }
    }

    Err(format!(
        "module '{}' not found (searched in: {})",
        module_name,
        search_paths
            .iter()
            .map(|p| p.display().to_string())
            .collect::<Vec<_>>()
            .join(", ")
    ))
}

pub fn load_and_register_imports(
    module_name: &str,
    type_env: &mut HashMap<String, Type>,
    functions: &mut HashMap<String, FunctionContext>,
) -> Result<(), String> {
    let path = find_mobj_file(module_name)?;
    let metadata = Metadata::from_mobj(&path)?;

    for export in metadata.exports {
        let fn_name = export.name;
        
        // Check for name conflicts
        if functions.contains_key(&fn_name) {
            return Err(format!(
                "function '{}' already defined (conflict with import from '{}')",
                fn_name, metadata.module_name
            ));
        }

        let param_types: Vec<Type> = export.params.iter().map(|(_, t)| t.clone()).collect();
        
        let fn_sig = FnSignature {
            params: param_types,
            ret: export.ret,
        };

        // Add to functions map for type checking
        let ctx = FunctionContext {
            symbols: HashMap::new(),
            fp_offset: 0,
            signature: fn_sig,
            param_names: export.params.iter().map(|(n, _)| n.clone()).collect(),
        };
        functions.insert(fn_name.clone(), ctx);

        // Also add to type_env for direct function calls
        type_env.insert(fn_name, Type::Int); // placeholder for now
    }

    Ok(())
}