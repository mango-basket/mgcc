use std::{
    iter::{Enumerate, Peekable},
    str::Bytes,
};

use crate::{
    error::{CompilerError, CompilerResult},
    tokenizer::token::{Keyword, Span, Token, TokenKind},
};

pub struct Lexer<'ip> {
    input: &'ip str,
    input_iter: Peekable<Enumerate<Bytes<'ip>>>,
}

impl<'ip> Lexer<'ip> {
    pub fn new(input: &'ip str) -> Self {
        Self {
            input,
            input_iter: input.bytes().enumerate().peekable(),
        }
    }

    fn is_ident(ch: &u8, is_starting: bool) -> bool {
        ch.is_ascii_alphabetic() || ch == &b'_' || (!is_starting && ch.is_ascii_digit())
    }

    fn get_int(&mut self, start_char: u8) -> CompilerResult<'ip, (TokenKind, usize)> {
        let mut int = ((start_char as u8) - b'0') as u16;
        let mut len = 1;
        while let Some((_, ch)) = self.input_iter.next_if(|(_, ch)| ch.is_ascii_digit()) {
            int = int
                .wrapping_mul(10)
                .wrapping_add(((ch as u8) - b'0') as u16);
            len += 1;
        }

        Ok((TokenKind::Int(int), len))
    }

    fn get_ident(&mut self, start_char: u8) -> CompilerResult<'ip, (TokenKind, usize)> {
        let mut ident = String::from(start_char as char);
        let mut len = 1;
        while let Some((_, ch)) = self.input_iter.next_if(|(_, ch)| Self::is_ident(ch, false)) {
            ident.push(ch as char);
            len += 1;
        }

        if ident == "true" || ident == "false" {
            Ok((TokenKind::Bool(ident == "true"), len))
        } else if let Some(keyword) = Keyword::from_string(&ident) {
            Ok((TokenKind::Keyword(keyword), len))
        } else {
            Ok((TokenKind::Identifier(ident.clone()), len))
        }
    }

    fn get_twochar_tok(
        &mut self,
        seconds: &[(u8, TokenKind)],
        fallback: TokenKind,
    ) -> CompilerResult<'ip, (TokenKind, usize)> {
        if let Some((_, ch)) = self.input_iter.peek() {
            for (expected_char, kind) in seconds {
                if ch == expected_char {
                    self.input_iter.next(); // consume the matched char
                    return Ok((kind.clone(), 2));
                }
            }
        }
        Ok((fallback, 1))
    }

    fn get_line_end(&mut self) -> usize {
        let mut length = 1;
        while let Some((_, cur)) = self.input_iter.peek() {
            if *cur == b'\n' || *cur == b';' {
                length += 1;
                self.input_iter.next();
            } else {
                break;
            }
        }

        length
    }

    fn get_char(&mut self) -> CompilerResult<'ip, (TokenKind, usize)> {
        // get exactly 1 byte
        let (pos, mut byte) = self.input_iter.next().ok_or(CompilerError::UnexpectedEof)?;
        let mut size = 3;

        // check for end of string, or escape characters
        match byte {
            b'\\' => {
                size += 1;
                // read n|\|'
                let escape = self.input_iter.next().ok_or(CompilerError::UnexpectedEof)?;
                byte = match escape.1 {
                    b'n' => b'\n',
                    b'\\' => b'\\',
                    b'\'' => b'\'',
                    x => {
                        return Err(CompilerError::LexerError(
                            format!("Invalid escape sequence '\\{}'", x as char),
                            Span::new(escape.0, escape.0 + 1, self.input),
                        ))
                    }
                };
            }
            b'\'' => {
                // raise an error for empty character
                return Err(CompilerError::LexerError(
                    "char literal cannot be empty".into(),
                    Span::new(pos, pos + 1, self.input),
                ));
            }
            _ => {}
        }

        // step over the last '
        match self.input_iter.next().ok_or(CompilerError::UnexpectedEof)? {
            (_, b'\'') => {}
            (pos, x) => {
                return Err(CompilerError::LexerError(
                    format!("expected \' found '{}'", x as char),
                    Span::new(pos, pos + 1, self.input),
                ))
            }
        }

        Ok((TokenKind::Char(byte), size))
    }
}

impl<'ip> Iterator for Lexer<'ip> {
    type Item = CompilerResult<'ip, Token<'ip>>;
    fn next(&mut self) -> Option<Self::Item> {
        let (start, cur) = self.input_iter.next()?;

        // handle // comments
        if cur == b'/' {
            if let Some((_, next_ch)) = self.input_iter.peek() {
                if *next_ch == b'/' {
                    // consume the second '/'
                    self.input_iter.next();

                    // consume until end of line
                    while let Some((_, ch)) = self.input_iter.next() {
                        if ch == b'\n' {
                            break;
                        }
                    }

                    // skip the comment and return next token
                    return self.next();
                }
            }

            // if not a comment, it's a normal slash token
            return Some(Ok(Token::new(
                TokenKind::Slash,
                Span::new(start, 1, self.input),
            )));
        }

        let result = match cur {
            b';' | b'\n' => Ok((TokenKind::LineEnd, self.get_line_end())),
            b'\'' => self.get_char(),
            b'+' => Ok((TokenKind::Plus, 1)),
            b'*' => Ok((TokenKind::Star, 1)),
            b'/' => Ok((TokenKind::Slash, 1)),
            b'%' => Ok((TokenKind::Mod, 1)),
            b'@' => Ok((TokenKind::Ref, 1)),
            b'(' => Ok((TokenKind::Lparen, 1)),
            b')' => Ok((TokenKind::Rparen, 1)),
            b'{' => Ok((TokenKind::Lbrace, 1)),
            b'}' => Ok((TokenKind::Rbrace, 1)),
            b'[' => Ok((TokenKind::Lsquare, 1)),
            b']' => Ok((TokenKind::Rsquare, 1)),
            b':' => Ok((TokenKind::Colon, 1)),
            b'^' => Ok((TokenKind::Xor, 1)),
            b'~' => Ok((TokenKind::Bnot, 1)),
            b',' => Ok((TokenKind::Comma, 1)),
            b'-' => self.get_twochar_tok(&[(b'>', TokenKind::Arrow)], TokenKind::Minus),
            b'&' => self.get_twochar_tok(&[(b'&', TokenKind::And)], TokenKind::Band),
            b'|' => self.get_twochar_tok(&[(b'|', TokenKind::Or)], TokenKind::Bor),
            b'=' => self.get_twochar_tok(&[(b'=', TokenKind::Eq)], TokenKind::Assign),
            b'!' => self.get_twochar_tok(&[(b'=', TokenKind::Neq)], TokenKind::Not),
            b'<' => self.get_twochar_tok(
                &[(b'=', TokenKind::Lte), (b'<', TokenKind::Shl)],
                TokenKind::Lt,
            ),
            b'>' => self.get_twochar_tok(
                &[(b'=', TokenKind::Gte), (b'>', TokenKind::Shr)],
                TokenKind::Gt,
            ),
            ws if (ws as char).is_whitespace() => return self.next(),
            ch if ch.is_ascii_digit() => self.get_int(ch),
            ch if Self::is_ident(&ch, true) => self.get_ident(ch),
            unknown => {
                return Some(Err(CompilerError::UnknownChar {
                    ch: unknown as char,
                    slice: Span::new(start, start + 1, self.input),
                }))
            }
        };

        if let Ok((kind, len)) = result {
            return Some(Ok(Token::new(
                kind,
                Span::new(start, start + len, self.input),
            )));
        } else {
            return Some(Err(result.err().unwrap()));
        }
    }
}
