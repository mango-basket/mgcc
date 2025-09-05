use crate::lexer::{Keyword, Slice, Token, TokenKind};
use std::{
    iter::{Enumerate, Peekable},
    str::Chars,
};

use crate::error::{CompilerError, CompilerResult};
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
        let mut int = ((start_char as u8) - b'0') as u16;
        let mut len = 1;
        while let Some((_, ch)) = self.input_iter.next_if(|(_, ch)| ch.is_ascii_digit()) {
            int = int
                .wrapping_mul(10)
                .wrapping_add(((ch as u8) - b'0') as u16);
            len += 1;
        }

        (TokenKind::Int(int), len)
    }

    fn get_ident(&mut self, start_char: char) -> (TokenKind, usize) {
        let mut ident = String::from(start_char);
        let mut len = 1;
        while let Some((_, ch)) = self.input_iter.next_if(|(_, ch)| Self::is_ident(ch, false)) {
            ident.push(ch);
            len += 1;
        }

        if ident == "true" || ident == "false" {
            (TokenKind::Bool(ident == "true"), len)
        } else if let Some(keyword) = Keyword::from_string(&ident) {
            (TokenKind::Keyword(keyword), len)
        } else {
            (TokenKind::Identifier(ident.clone()), len)
        }
    }

    fn get_twochar_tok(
        &mut self,
        second: (char, TokenKind),
        fallback: TokenKind,
    ) -> (TokenKind, usize) {
        if let Some(_) = self.input_iter.next_if(|(_, ch)| ch == &second.0) {
            (second.1, 2)
        } else {
            (fallback, 1)
        }
    }

    fn get_line_end(&mut self) -> usize {
        let mut length = 1;
        while let Some((_, cur)) = self.input_iter.peek() {
            if ";\n".contains(*cur) {
                length += 1;
                self.input_iter.next();
            } else {
                break;
            }
        }

        length
    }
}

impl<'ip> Iterator for Lexer<'ip> {
    type Item = CompilerResult<'ip, Token<'ip>>;
    fn next(&mut self) -> Option<Self::Item> {
        let (start, cur) = self.input_iter.next()?;
        let (kind, len) = match cur {
            ';' | '\n' => (TokenKind::LineEnd, self.get_line_end()),
            '+' => (TokenKind::Plus, 1),
            '-' => (TokenKind::Minus, 1),
            '*' => (TokenKind::Star, 1),
            '/' => (TokenKind::Slash, 1),
            '(' => (TokenKind::Lparen, 1),
            ')' => (TokenKind::Rparen, 1),
            ':' => (TokenKind::Colon, 1),
            '=' => self.get_twochar_tok(('=', TokenKind::Eq), TokenKind::Assign),
            '!' => self.get_twochar_tok(('=', TokenKind::Neq), TokenKind::Not),
            '<' => self.get_twochar_tok(('=', TokenKind::Lte), TokenKind::Lt),
            '>' => self.get_twochar_tok(('=', TokenKind::Gte), TokenKind::Gt),
            ws if ws.is_whitespace() => return self.next(),
            ch if ch.is_ascii_digit() => self.get_int(ch),
            ch if Self::is_ident(&ch, true) => self.get_ident(ch),
            unknown => return Some(Err(CompilerError::UnknownChar(unknown))),
        };

        Some(Ok(Token::new(kind, Slice::new(start, len, self.input))))
    }
}
