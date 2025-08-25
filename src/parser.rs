use std::iter::Peekable;

use crate::{
    error::{CompilerError, CompilerResult},
    lexer::{Keyword, Lexer, Token, TokenKind},
};

#[derive(Debug)]
pub enum Ast<'ip> {
    Identifier(Token<'ip>),
    Int(Token<'ip>),
    Bool(Token<'ip>),
    UnaryOp {
        op: Token<'ip>,
        operand: Box<Ast<'ip>>,
    },
    BinaryOp {
        left: Box<Ast<'ip>>,
        op: Token<'ip>,
        right: Box<Ast<'ip>>,
    },
    Assign {
        name: Token<'ip>,
        vartype: Token<'ip>,
        rhs: Box<Ast<'ip>>,
    },
    Statements(Vec<Box<Ast<'ip>>>),
}

fn parse_binary_op<'ip, F>(
    lexer: &mut Peekable<Lexer<'ip>>,
    operators: &[TokenKind],
    subparser: F,
) -> CompilerResult<'ip, Ast<'ip>>
where
    F: Fn(&mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>>,
{
    let mut node = subparser(lexer)?;

    while let Some(Ok(tok)) =
        lexer.next_if(|tok| matches!(tok, Ok(x) if operators.contains(&x.kind)))
    {
        node = Ast::BinaryOp {
            left: Box::new(node),
            op: tok,
            right: Box::new(subparser(lexer)?),
        };
    }

    Ok(node)
}

pub fn parse<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    parse_statements(lexer)
}

fn parse_statements<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    let mut stmts = Vec::new();

    while let Some(peek) = lexer.peek() {
        match peek {
            Ok(_) => {
                let stmt = parse_statement(lexer)?;
                stmts.push(Box::new(stmt));
            }
            Err(_) => {
                return Err(lexer.next().unwrap().unwrap_err());
            }
        }
    }

    Ok(Ast::Statements(stmts))
}

fn parse_statement<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    if let Some(Ok(tok)) = lexer.peek() {
        match tok.kind {
            // Variable definition
            TokenKind::Keyword(Keyword::Var) => {
                let _ = lexer.next().ok_or(CompilerError::UnexpectedEof)??;

                let name = match lexer.next().ok_or(CompilerError::UnexpectedEof)?? {
                    tok if matches!(tok.kind, TokenKind::Identifier(_)) => tok,
                    got => {
                        return Err(CompilerError::UnexpectedToken {
                            got,
                            expected: "identifier",
                        })
                    }
                };

                let colon = lexer.next().ok_or(CompilerError::UnexpectedEof)??;
                if !matches!(colon.kind, TokenKind::Colon) {
                    return Err(CompilerError::UnexpectedToken {
                        got: colon,
                        expected: ":",
                    });
                }

                let vartype = match lexer.next().ok_or(CompilerError::UnexpectedEof)?? {
                    tok if matches!(tok.kind, TokenKind::Identifier(_)) => tok,
                    got => {
                        return Err(CompilerError::UnexpectedToken {
                            got,
                            expected: "type identifier",
                        })
                    }
                };

                let eq = lexer.next().ok_or(CompilerError::UnexpectedEof)??;
                if !matches!(eq.kind, TokenKind::Assign) {
                    return Err(CompilerError::UnexpectedToken {
                        got: eq,
                        expected: "=",
                    });
                }

                let rhs = parse_expression(lexer)?;

                let lineend = lexer.next().ok_or(CompilerError::UnexpectedEof)??;
                if !matches!(lineend.kind, TokenKind::LineEnd) {
                    return Err(CompilerError::UnexpectedToken {
                        got: lineend,
                        expected: "line end",
                    });
                }

                Ok(Ast::Assign {
                    name,
                    vartype,
                    rhs: Box::new(rhs),
                })
            }
            _ => parse_expression(lexer),
        }
    } else {
        parse_expression(lexer)
    }
}

fn parse_expression<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    parse_comparison(lexer)
}

fn parse_comparison<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    parse_binary_op(lexer, &[TokenKind::Eq, TokenKind::Neq], parse_relational)
}

fn parse_relational<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    parse_binary_op(
        lexer,
        &[TokenKind::Gt, TokenKind::Gte, TokenKind::Lt, TokenKind::Lte],
        parse_additive,
    )
}

fn parse_additive<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    parse_binary_op(
        lexer,
        &[TokenKind::Plus, TokenKind::Minus],
        parse_multiplicative,
    )
}

fn parse_multiplicative<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    parse_binary_op(lexer, &[TokenKind::Star, TokenKind::Slash], parse_atom)
}

fn parse_atom<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    // if lexer returns none, we have an unexpected EOF error
    let token = lexer.next().ok_or(CompilerError::UnexpectedEof)??;
    let node = match token.kind {
        TokenKind::LineEnd => parse(lexer)?,
        TokenKind::Int(_) => Ast::Int(token),
        TokenKind::Identifier(_) => Ast::Identifier(token),
        TokenKind::Bool(_) => Ast::Bool(token),
        TokenKind::Minus | TokenKind::Not => Ast::UnaryOp {
            op: token,
            operand: Box::new(parse_atom(lexer)?),
        },
        TokenKind::Lparen => {
            let node = parse_comparison(lexer)?;

            match lexer.next() {
                Some(Ok(tok)) if matches!(tok.kind, TokenKind::Rparen) => node,
                Some(Ok(got)) => return Err(CompilerError::UnexpectedToken { got, expected: ")" }),
                _ => return Err(CompilerError::UnexpectedEof),
            }
        }
        _ => {
            return Err(CompilerError::UnexpectedToken {
                got: token,
                expected: "int', 'bool', '!', '(', '-' or 'ident",
            })
        }
    };

    Ok(node)
}
