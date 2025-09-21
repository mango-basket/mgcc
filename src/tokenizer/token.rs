use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Keyword {
    Var,
    If,
    Else,
    Loop,
    Break,
    Continue,
    Disp,
    Fn,
    Return,
}

impl Keyword {
    pub fn from_string(string: &str) -> Option<Keyword> {
        match string {
            "var" => Some(Keyword::Var),
            "if" => Some(Keyword::If),
            "else" => Some(Keyword::Else),
            "loop" => Some(Keyword::Loop),
            "continue" => Some(Keyword::Continue),
            "break" => Some(Keyword::Break),
            "disp" => Some(Keyword::Disp),
            "fn" => Some(Keyword::Fn),
            "return" => Some(Keyword::Return),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenKind {
    Int(u16),
    // Float(f32),
    Bool(bool),
    Keyword(Keyword),
    Identifier(String),
    // String(String),
    Plus,
    Minus,
    Star,
    Slash,
    Mod,
    Ref,
    And,
    Or,
    Band,
    Bor,
    Xor,
    Bnot,
    Shl,
    Shr,
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
    Lbrace,
    Rbrace,
    Comma,
    Arrow,
}

impl TokenKind {
    //     pub fn get_static_str(&self) -> &'static str {
    //         match self {
    //             TokenKind::Eq => "==",
    //             TokenKind::Neq => "!=",
    //             TokenKind::Lt => "<",
    //             TokenKind::Gt => ">",
    //             TokenKind::Lte => "<=",
    //             TokenKind::Gte => ">=",
    //             TokenKind::Assign => "=",
    //             TokenKind::Plus => "+",
    //             TokenKind::Minus => "-",
    //             TokenKind::Star => "*",
    //             TokenKind::Slash => "/",
    //             TokenKind::Lparen => "(",
    //             TokenKind::Rparen => ")",
    //             TokenKind::Lbrace => "{",
    //             TokenKind::Rbrace => "}",
    //             TokenKind::Colon => ":",
    //             TokenKind::LineEnd => "end of line",
    //             TokenKind::Identifier(_) => "identifier",
    //             TokenKind::Int(_) => "integer literal",
    //             TokenKind::Bool(_) => "boolean literal",
    //             TokenKind::Not => "!",
    //             TokenKind::Keyword(k) => match k {
    //                 Keyword::Var => "var",
    //                 Keyword::If => "if",
    //                 Keyword::Else => "else",
    //                 Keyword::Loop => "loop",
    //                 Keyword::Break => "break",
    //                 Keyword::Continue => "continue",
    //                 Keyword::Disp => "disp",
    //                 Keyword::Fn => "fn",
    //                 Keyword::Return => "return",
    //             },
    //             TokenKind::And => "&&",
    //             TokenKind::Or => "||",
    //             TokenKind::Band => "&",
    //             TokenKind::Bor => "|",
    //             TokenKind::Xor => "^",
    //             TokenKind::Bnot => "~",
    //             TokenKind::Shl => "<<",
    //             TokenKind::Shr => ">>",
    //             TokenKind::Mod => "%",
    //             TokenKind::Ref => "@",
    //             TokenKind::Comma => ",",
    //             TokenKind::Arrow => "->",
    //         }
    //     }
}

#[derive(Clone, Default)]
pub struct Span<'ip> {
    pub start: usize,
    pub end: usize,
    pub input: &'ip str,
}

impl<'ip> fmt::Debug for Span<'ip> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let snippet = &self.input[self.start..self.end];
        f.debug_struct("Slice")
            .field("start", &self.start)
            .field("len", &(self.end - self.start))
            .field("text", &snippet)
            .finish()
    }
}

impl<'ip> Span<'ip> {
    pub fn new(start: usize, end: usize, input: &'ip str) -> Self {
        Self { start, end, input }
    }

    pub fn get_str(&self) -> &str {
        if let Some(str) = self.input.get(self.start..self.end) {
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

impl<'ip> fmt::Display for Span<'ip> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'{}' at {}", self.get_str(), self.get_row_col())
    }
}

#[derive(Debug, Clone)]
pub struct Token<'ip> {
    pub kind: TokenKind,
    pub slice: Span<'ip>,
}

impl<'ip> Token<'ip> {
    pub fn new(kind: TokenKind, slice: Span<'ip>) -> Self {
        Self { kind, slice }
    }
}
