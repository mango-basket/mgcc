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
    As,
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
            "as" => Some(Keyword::As),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenKind {
    Int(u16),
    Bool(bool),
    Keyword(Keyword),
    Identifier(String),
    Char(u8),
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
    Lsquare,
    Rsquare,
    Comma,
    Arrow,
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
    pub span: Span<'ip>,
}

impl<'ip> Token<'ip> {
    pub fn new(kind: TokenKind, slice: Span<'ip>) -> Self {
        Self { kind, span: slice }
    }
}
