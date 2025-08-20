use crate::lexer::Token;
use std::{error::Error, fmt::Display};

#[derive(Debug)]
pub enum CompilerError<'ip> {
    UnknownChar(char),
    UnexpectedToken {
        got: Token<'ip>,
        expected: &'static str,
    },
    UnexpectedEof,
    RuntimeError(String),
}

impl<'ip> Display for CompilerError<'ip> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownChar(ch) => write!(f, "LexerError: unknown character '{}'", ch),
            Self::UnexpectedToken { got, expected } => {
                write!(f, "Expected token '{:?}' found '{}'", got.kind, expected)
            }
            Self::UnexpectedEof => write!(f, "Unexpected EOF"),
            Self::RuntimeError(err) => write!(f, "Runtime Error: {}", err),
        }
    }
}

impl<'ip> Error for CompilerError<'ip> {}
pub type CompilerResult<'ip, T> = Result<T, CompilerError<'ip>>;

#[derive(Debug)]
pub struct RuntimeError(pub String);
impl Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RuntimeError: {}", self.0)
    }
}

impl Error for RuntimeError {}
pub type RuntimeResult<T> = Result<T, RuntimeError>;
