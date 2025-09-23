use std::{error::Error, fmt::Display};

use crate::{
    semantic::type_check::Type,
    tokenizer::token::{Span, Token},
};

#[derive(Debug, Clone)]
pub enum CompilerError<'ip> {
    UnknownChar {
        ch: char,
        slice: Span<'ip>,
    },
    LexerError(String, Span<'ip>),
    UnexpectedToken {
        got: Token<'ip>,
        expected: &'static str,
    },
    UnexpectedType {
        got: Type,
        expected: String,
        slice: Span<'ip>,
    },
    UnexpectedEof,
    OpTypeError {
        op: Token<'ip>,
        lhs: Option<Type>,
        rhs: Type,
    },
    TypeError(String, Span<'ip>),
    UndefinedIdentifier(Span<'ip>),
    Semantic {
        err: String,
        span: Span<'ip>,
    },
}

impl<'ip> Display for CompilerError<'ip> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownChar { ch, slice } => {
                write!(
                    f,
                    "LexerError at {}: unknown character '{}'",
                    slice.get_row_col(),
                    ch
                )
            }
            Self::UnexpectedToken { got, expected } => {
                write!(
                    f,
                    "ParserError at {}: expected '{}' but found token '{:?}'",
                    got.span.get_row_col(),
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
            Self::TypeError(err, slice) => {
                write!(f, "TypeError at {}: {}", slice.get_row_col(), err)
            }
            Self::OpTypeError { op, lhs, rhs } => {
                if let Some(lhs) = lhs {
                    write!(
                        f,
                        "TypeError at {}: cannot apply operator '{}' between '{}' and '{}'",
                        op.span.get_row_col(),
                        op.span.get_str(),
                        lhs.to_string(),
                        rhs.to_string(),
                    )
                } else {
                    write!(
                        f,
                        "TypeError at {}: cannot apply operator '{}' to '{}'",
                        op.span.get_row_col(),
                        op.span.get_str(),
                        rhs.to_string(),
                    )
                }
            }
            Self::UndefinedIdentifier(slice) => {
                write!(
                    f,
                    "NameError at {}: undefined identifier '{}'",
                    slice.get_row_col(),
                    slice.get_str()
                )
            }
            Self::Semantic { err, span: slice } => {
                write!(f, "Semantic Error at {}: {}", slice.get_row_col(), err)
            }
            Self::LexerError(err, span) => {
                write!(f, "LexerError at {}: {}", span.get_row_col(), err)
            }
        }
    }
}

impl<'ip> Error for CompilerError<'ip> {}
pub type CompilerResult<'ip, T> = Result<T, CompilerError<'ip>>;
