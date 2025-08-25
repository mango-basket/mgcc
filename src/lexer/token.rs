use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Keyword {
    Var,
}

impl Keyword {
    pub fn from_string(string: &str) -> Option<Keyword> {
        match string {
            "var" => Some(Self::Var),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenKind {
    Int(u32),
    // Float(f32),
    Bool(bool),
    Keyword(Keyword),
    Identifier(String),
    // String(String),
    Plus,
    Minus,
    Star,
    Slash,
    Not,
    Gt,
    Gte,
    Lt,
    Lte,
    Eq,
    Neq,
    Assign,
    Colon,
    LineEnd,
    Lparen,
    Rparen,
}

impl TokenKind {
    pub fn type_name(&self) -> &'static str {
        match self {
            TokenKind::Int(_) => "Int",
            TokenKind::Bool(_) => "Bool",
            TokenKind::Keyword(_) => "Keyword",
            TokenKind::Identifier(_) => "Identifier",
            TokenKind::Plus => "Plus",
            TokenKind::Minus => "Minus",
            TokenKind::Star => "Star",
            TokenKind::Slash => "Slash",
            TokenKind::Not => "Not",
            TokenKind::Gt => "Gt",
            TokenKind::Gte => "Gte",
            TokenKind::Lt => "Lt",
            TokenKind::Lte => "Lte",
            TokenKind::Eq => "Eq",
            TokenKind::Neq => "Neq",
            TokenKind::Assign => "Assign",
            TokenKind::Colon => "Colon",
            TokenKind::LineEnd => "LineEnd",
            TokenKind::Lparen => "LParen",
            TokenKind::Rparen => "RParen",
        }
    }
}

#[derive(Debug, Clone)]
pub struct Slice<'ip> {
    start: usize,
    len: usize,
    input: &'ip str,
}

impl<'ip> Slice<'ip> {
    pub fn get_str(&self) -> &str {
        if let Some(str) = self.input.get(self.start..self.start + self.len) {
            str
        } else {
            "<unprintable>"
        }
    }

    pub fn get_row_col(&self) -> String {
        let mut row = 1;
        let mut col = 1;

        for (i, ch) in self.input.chars().enumerate() {
            if i == self.start {
                break;
            }
            if ch == '\n' {
                row += 1;
                col = 1;
            } else {
                col += 1;
            }
        }

        format!("{}:{}", row, col)
    }
}

impl<'ip> fmt::Display for Slice<'ip> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'{}' at {}", self.get_str(), self.get_row_col())
    }
}

impl<'ip> Slice<'ip> {
    pub fn new(start: usize, len: usize, input: &'ip str) -> Self {
        Self { start, len, input }
    }
}

#[derive(Debug, Clone)]
pub struct Token<'ip> {
    pub kind: TokenKind,
    pub slice: Slice<'ip>,
}

impl<'ip> Token<'ip> {
    pub fn new(kind: TokenKind, slice: Slice<'ip>) -> Self {
        Self { kind, slice }
    }
}
