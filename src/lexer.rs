use std::{
    iter::{Enumerate, Peekable},
    str::Chars,
};

use crate::error::{CompilerError, CompilerResult};

#[derive(Debug, PartialEq, Eq)]
pub enum TokenKind {
    Uint(u32),
    // Float(f32),
    // Bool(bool),
    // Keyword(Keyword),
    Identifier(String),
    // String(String),
    Plus,
    Minus,
    Star,
    Slash,
    Eq,
    Semicolon,
    Lparen,
    Rparen,
}

#[derive(Debug)]
pub struct Slice<'ip> {
    start: usize,
    len: usize,
    input: &'ip str,
}

impl<'ip> Slice<'ip> {
    pub fn get_string(&self) -> &str {
        if let Some(str) = self.input.get(self.start..self.start + self.len) {
            str
        } else {
            "<unprintable>"
        }
    }
}

impl<'ip> Slice<'ip> {
    pub fn new(start: usize, len: usize, input: &'ip str) -> Self {
        Self { start, len, input }
    }
}

#[derive(Debug)]
pub struct Token<'ip> {
    pub kind: TokenKind,
    slice: Slice<'ip>,
}

impl<'ip> Token<'ip> {
    pub fn new(kind: TokenKind, slice: Slice<'ip>) -> Self {
        Self { kind, slice }
    }
}

pub struct Lexer<'ip> {
    input: &'ip str,
    input_iter: Peekable<Enumerate<Chars<'ip>>>,
}

impl<'ip> Lexer<'ip> {
    pub fn new(input: &'ip str) -> Self {
        Self {
            input,
            input_iter: input.chars().enumerate().peekable(),
        }
    }

    fn is_ident(ch: &char, is_starting: bool) -> bool {
        ch.is_ascii_alphabetic() || ch == &'_' || (!is_starting && ch.is_ascii_digit())
    }

    fn get_int(&mut self, start_char: char) -> (TokenKind, usize) {
        let mut int = ((start_char as u8) - b'0') as u32;
        let mut len = 1;
        while let Some((_, ch)) = self.input_iter.next_if(|(_, ch)| ch.is_ascii_digit()) {
            int = int * 10 + ((ch as u8) - b'0') as u32;
            len += 1;
        }

        (TokenKind::Uint(int), len)
    }

    fn get_ident(&mut self, start_char: char) -> (TokenKind, usize) {
        let mut ident = String::from(start_char);
        let mut len = 1;
        while let Some((_, ch)) = self.input_iter.next_if(|(_, ch)| Self::is_ident(ch, false)) {
            ident.push(ch);
            len += 1;
        }
        (TokenKind::Identifier(ident), len)
    }
}

impl<'ip> Iterator for Lexer<'ip> {
    type Item = CompilerResult<'ip, Token<'ip>>;
    fn next(&mut self) -> Option<Self::Item> {
        let (start, cur) = self.input_iter.next()?;
        let (kind, len) = match cur {
            '+' => (TokenKind::Plus, 1),
            '-' => (TokenKind::Minus, 1),
            '*' => (TokenKind::Star, 1),
            '/' => (TokenKind::Slash, 1),
            ';' => (TokenKind::Semicolon, 1),
            '(' => (TokenKind::Lparen, 1),
            ')' => (TokenKind::Rparen, 1),
            '=' => (TokenKind::Eq, 1),
            ws if ws.is_whitespace() => return self.next(),
            ch if ch.is_ascii_digit() => self.get_int(ch),
            // ch if Self::is_ident(&ch, true) => self.get_ident(ch),
            unknown => return Some(Err(CompilerError::UnknownChar(unknown))),
        };

        Some(Ok(Token::new(kind, Slice::new(start, len, self.input))))
    }
}
