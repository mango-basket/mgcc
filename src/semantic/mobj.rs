use std::{collections::HashMap, fs, path::Path};

use crate::{
    error::{CompilerError, CompilerResult},
    semantic::type_check::{FnSignature, Type},
    tokenizer::token::Span,
};

#[derive(Debug, Clone)]
pub struct ExportInfo {
    pub name: String,
    pub params: Vec<(String, Type)>, // (name, type)
    pub ret: Type,
}

#[derive(Debug, Default)]
pub struct StringPool {
    strings: Vec<String>,
    offsets: HashMap<String, u16>,
}

impl StringPool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, s: &str) -> u16 {
        if let Some(&offset) = self.offsets.get(s) {
            return offset;
        }
        let offset = self.strings.len() as u16;
        self.strings.push(s.to_owned());
        self.offsets.insert(s.to_owned(), offset);
        offset
    }

    pub fn resolve(&self, offset: u16) -> &str {
        self.strings.get(offset as usize).map(|s| s.as_str()).unwrap_or("")
    }

    pub fn from_bytes(data: &[u8]) -> Self {
        let mut strings = Vec::new();
        let mut offsets = HashMap::new();
        let mut start = 0;

        for (i, &b) in data.iter().enumerate() {
            if b == 0 {
                let s = String::from_utf8_lossy(&data[start..i]).into_owned();
                offsets.insert(s.clone(), start as u16);
                strings.push(s);
                start = i + 1;
            }
        }

        Self { strings, offsets }
    }
}

#[derive(Debug)]
struct Export {
    name_ofst: u16,
    ret_ofst: u16,
    first_param_ofst: u16,
    param_count: u16,
}

#[derive(Debug)]
struct Param {
    name_ofst: u16,
    type_ofst: u16,
}

fn read_u16(data: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes([data[offset], data[offset + 1]])
}

pub fn load_mobj_metadata<P: AsRef<Path>>(path: P) -> CompilerResult<'static, Vec<ExportInfo>> {
    let bytes = fs::read(path).map_err(|e| CompilerError::Semantic {
        err: format!("failed to read MOBJ file: {e}"),
        span: Span::new(0, 0, ""),
    })?;

    if bytes.len() < 16 || &bytes[0..4] != b"MOBJ" {
        return Err(CompilerError::Semantic {
            err: "invalid MOBJ file: bad magic".to_string(),
            span: Span::new(0, 0, ""),
        });
    }

    let version = read_u16(&bytes, 4);
    if version < 3 {
        return Err(CompilerError::Semantic {
            err: format!("MOBJ version {} does not contain metadata (requires version 3+)", version),
            span: Span::new(0, 0, ""),
        });
    }

    let instr_bytes_len = read_u16(&bytes, 6) as usize;
    let data_bytes_len = read_u16(&bytes, 8) as usize;
    let symtable_len = read_u16(&bytes, 10) as usize;
    let reloctable_len = read_u16(&bytes, 12) as usize;
    let meta_len = read_u16(&bytes, 14) as usize;

    if meta_len == 0 {
        return Err(CompilerError::Semantic {
            err: "MOBJ file has no metadata section".to_string(),
            span: Span::new(0, 0, ""),
        });
    }

    let meta_start = 16 + instr_bytes_len + data_bytes_len + symtable_len + reloctable_len;
    let meta_end = meta_start + meta_len;

    if meta_end > bytes.len() {
        return Err(CompilerError::Semantic {
            err: "metadata section extends beyond file".to_string(),
            span: Span::new(0, 0, ""),
        });
    }

    let meta_data = &bytes[meta_start..meta_end];

    if meta_data.len() < 8 {
        return Err(CompilerError::Semantic {
            err: "metadata section too small".to_string(),
            span: Span::new(0, 0, ""),
        });
    }

    let name_ofst = read_u16(meta_data, 0);
    let dependency_count = read_u16(meta_data, 2);
    let export_count = read_u16(meta_data, 4);
    let param_count = read_u16(meta_data, 6);

    let mut pos = 8;

    // Skip dependencies
    pos += dependency_count as usize * 2;

    // Parse exports
    let mut exports = Vec::new();
    for _ in 0..export_count {
        let export = Export {
            name_ofst: read_u16(meta_data, pos),
            ret_ofst: read_u16(meta_data, pos + 2),
            first_param_ofst: read_u16(meta_data, pos + 4),
            param_count: read_u16(meta_data, pos + 6),
        };
        exports.push(export);
        pos += 8;
    }

    // Parse params
    let mut params = Vec::new();
    for _ in 0..param_count {
        params.push(Param {
            name_ofst: read_u16(meta_data, pos),
            type_ofst: read_u16(meta_data, pos + 2),
        });
        pos += 4;
    }

    // String pool
    let string_pool = StringPool::from_bytes(&meta_data[pos..]);

    // Build export info
    let mut result = Vec::new();
    for export in exports {
        let name = string_pool.resolve(export.name_ofst).to_string();
        let ret = string_pool.resolve(export.ret_ofst).to_string();
        let ret_type = parse_type(&ret)?;

        let mut param_list = Vec::new();
        for i in 0..export.param_count {
            let idx = export.first_param_ofst as usize + i as usize;
            let param = &params[idx];
            let pname = string_pool.resolve(param.name_ofst).to_string();
            let ptype_str = string_pool.resolve(param.type_ofst).to_string();
            let ptype = parse_type(&ptype_str)?;
            param_list.push((pname, ptype));
        }

        result.push(ExportInfo {
            name,
            params: param_list,
            ret: ret_type,
        });
    }

    Ok(result)
}

fn parse_type(s: &str) -> CompilerResult<'static, Type> {
    let s = s.trim();
    match s {
        "int" => Ok(Type::Int),
        "bool" => Ok(Type::Bool),
        "unit" => Ok(Type::Unit),
        "void" => Ok(Type::Unit),
        "char" => Ok(Type::Char),
        "raw" => Ok(Type::Raw),
        s if s.starts_with("ref ") => {
            let inner = s.trim_start_matches("ref ").trim();
            let inner_type = parse_type(inner)?;
            Ok(Type::Ref(Box::new(inner_type)))
        }
        s if s.starts_with("fn (") => {
            // fn (param1: type1, ...) -> rettype
            let inner = s.trim_start_matches("fn (").trim();
            let (params_part, ret_part) = inner.split_once(") -> ").ok_or_else(|| CompilerError::Semantic {
                err: format!("invalid function type: {s}"),
                span: Span::new(0, 0, ""),
            })?;
            let ret = parse_type(ret_part.trim())?;
            let params = if params_part.trim().is_empty() {
                Vec::new()
            } else {
                params_part
                    .split(',')
                    .map(|p| {
                        let (_, ty) = p.trim().split_once(':').ok_or_else(|| CompilerError::Semantic {
                            err: format!("invalid param: {p}"),
                            span: Span::new(0, 0, ""),
                        })?;
                        parse_type(ty.trim())
                    })
                    .collect::<Result<Vec<_>, _>>()?
            };
            Ok(Type::Fn { params, ret: Box::new(ret) })
        }
        _ => Err(CompilerError::Semantic {
            err: format!("unknown type: {s}"),
            span: Span::new(0, 0, ""),
        }),
    }
}

pub fn find_mobj_file(module_name: &str) -> CompilerResult<'_, std::path::PathBuf> {
    // First check current working directory
    let cwd = std::env::current_dir().map_err(|e| CompilerError::Semantic {
        err: format!("failed to get CWD: {e}"),
        span: Span::new(0, 0, ""),
    })?;
    let cwd_path = cwd.join(format!("{module_name}.mobj"));
    if cwd_path.exists() {
        return Ok(cwd_path);
    }

    // Then check MANGO_PATHS
    let paths = std::env::var("MANGO_PATHS").map_err(|_| CompilerError::Semantic {
        err: "MANGO_PATHS environment variable not set".to_string(),
        span: Span::new(0, 0, ""),
    })?;

    for path_str in paths.split(':') {
        let path = Path::new(path_str).join(format!("{module_name}.mobj"));
        if path.exists() {
            return Ok(path);
        }
    }

    Err(CompilerError::Semantic {
        err: format!(
            "module '{module_name}' not found in MANGO_PATHS (searched: {})",
            paths
        ),
        span: Span::new(0, 0, ""),
    })
}