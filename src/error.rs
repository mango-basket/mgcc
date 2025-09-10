use crate::{
    lexer::{Slice, Token},
    type_check::Type,
};
use std::{error::Error, fmt::Display};

#[derive(Debug)]
pub enum CompilerError<'ip> {
    UnknownChar(char),
    UnexpectedToken {
        got: Token<'ip>,
        expected: &'static str,
    },
    UnexpectedType {
        got: Type,
        expected: String,
        slice: Slice<'ip>,
    },
    UnexpectedEof,
    OpTypeError {
        op: Token<'ip>,
        lhs: Option<Token<'ip>>,
        rhs: Token<'ip>,
    },
    TypeError(String),
    UndefinedIdentifier {
        ident: Token<'ip>,
    },
    Semantic(String),
}

impl<'ip> Display for CompilerError<'ip> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownChar(ch) => {
                write!(f, "LexerError: unknown character '{}'", ch)
            }
            Self::UnexpectedToken { got, expected } => {
                write!(
                    f,
                    "ParserError at {}: expected '{}' but found token '{:?}'",
                    got.slice.get_row_col(),
                    expected,
                    got.kind
                )
            }
            Self::UnexpectedType {
                got,
                expected,
                slice,
            } => {
                write!(
                    f,
                    "TypeError at {}: expected '{}' but found '{:?}'",
                    slice.get_row_col(),
                    expected,
                    got
                )
            }
            Self::UnexpectedEof => {
                write!(f, "ParserError: unexpected end of file")
            }
            Self::TypeError(err) => {
                write!(f, "TypeError: {}", err)
            }
            Self::OpTypeError { op, lhs, rhs } => {
                if let Some(lhs) = lhs {
                    write!(
                        f,
                        "TypeError at {}: cannot apply operator '{}' between '{}' and '{}'",
                        op.slice.get_row_col(),
                        op.slice.get_str(),
                        lhs.slice.get_str(),
                        rhs.slice.get_str(),
                    )
                } else {
                    write!(
                        f,
                        "TypeError at {}: cannot apply operator '{}' to '{}'",
                        op.slice.get_row_col(),
                        op.slice.get_str(),
                        rhs.slice.get_str(),
                    )
                }
            }
            Self::UndefinedIdentifier { ident } => {
                write!(
                    f,
                    "NameError at {}: undefined identifier '{}'",
                    ident.slice.get_row_col(),
                    ident.slice.get_str()
                )
            }
            CompilerError::Semantic(err) => write!(f, "Semantic Error: {}", err),
        }
    }
}

impl<'ip> Error for CompilerError<'ip> {}
pub type CompilerResult<'ip, T> = Result<T, CompilerError<'ip>>;
