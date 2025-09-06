use std::{collections::VecDeque, iter::Peekable};

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
        vartype: Option<Token<'ip>>,
        rhs: Box<Ast<'ip>>,
    },
    Reassign {
        name: Token<'ip>,
        rhs: Box<Ast<'ip>>,
    },
    Statements(Vec<Box<Ast<'ip>>>),
}

pub struct Parser<'ip> {
    lexer: Peekable<Lexer<'ip>>,
    buffer: VecDeque<CompilerResult<'ip, Token<'ip>>>,
}

impl<'ip> Parser<'ip> {
    pub fn new(lexer: Lexer<'ip>) -> Self {
        Self {
            lexer: lexer.peekable(),
            buffer: VecDeque::new(),
        }
    }

    pub fn peek_n(&mut self, n: usize) -> Option<&CompilerResult<'ip, Token<'ip>>> {
        while self.buffer.len() <= n {
            if let Some(tok) = self.lexer.next() {
                self.buffer.push_back(tok);
            } else {
                break;
            }
        }
        self.buffer.get(n)
    }

    pub fn next_token(&mut self) -> Option<CompilerResult<'ip, Token<'ip>>> {
        if let Some(tok) = self.buffer.pop_front() {
            Some(tok)
        } else {
            self.lexer.next()
        }
    }

    pub fn next_if<F>(&mut self, f: F) -> Option<CompilerResult<'ip, Token<'ip>>>
    where
        F: Fn(&Token<'ip>) -> bool,
    {
        match self.peek() {
            Some(Ok(tok)) if f(tok) => self.next_token(),
            _ => None,
        }
    }

    pub fn peek(&mut self) -> Option<&CompilerResult<'ip, Token<'ip>>> {
        self.peek_n(0)
    }

    fn expect_line_end(&mut self) -> CompilerResult<'ip, ()> {
        let tok = self.next_token().ok_or(CompilerError::UnexpectedEof)??;
        if !matches!(tok.kind, TokenKind::LineEnd) {
            return Err(CompilerError::UnexpectedToken {
                got: tok,
                expected: "line end",
            });
        }
        Ok(())
    }

    // -- Parse functions --

    pub fn parse(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_statements()
    }

    fn parse_statements(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        let mut stmts = Vec::new();

        while let Some(peek) = self.peek() {
            match peek {
                Ok(_) => {
                    let stmt = self.parse_statement()?;
                    stmts.push(Box::new(stmt));
                }
                Err(_) => {
                    return Err(self.next_token().unwrap().unwrap_err());
                }
            }
        }

        Ok(Ast::Statements(stmts))
    }

    fn parse_statement(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        if let Some(Ok(tok)) = self.peek() {
            match &tok.kind {
                // Variable definition
                TokenKind::Keyword(Keyword::Var) => {
                    let _ = self.next_token().ok_or(CompilerError::UnexpectedEof)??;

                    let name = match self.next_token().ok_or(CompilerError::UnexpectedEof)?? {
                        tok if matches!(tok.kind, TokenKind::Identifier(_)) => tok,
                        got => {
                            return Err(CompilerError::UnexpectedToken {
                                got,
                                expected: "identifier",
                            })
                        }
                    };

                    // look ahead for optional colon
                    let mut vartype = None;
                    if let Some(Ok(next)) = self.peek() {
                        if matches!(next.kind, TokenKind::Colon) {
                            let _ = self.next_token();

                            let t =
                                match self.next_token().ok_or(CompilerError::UnexpectedEof)?? {
                                    tok if matches!(tok.kind, TokenKind::Identifier(_)) => tok,
                                    got => {
                                        return Err(CompilerError::UnexpectedToken {
                                            got,
                                            expected: "type identifier",
                                        })
                                    }
                                };

                            vartype = Some(t)
                        }
                    }

                    let eq = self.next_token().ok_or(CompilerError::UnexpectedEof)??;
                    if !matches!(eq.kind, TokenKind::Assign) {
                        return Err(CompilerError::UnexpectedToken {
                            got: eq,
                            expected: "=",
                        });
                    }

                    let rhs = self.parse_expression()?;
                    self.expect_line_end()?;

                    Ok(Ast::Assign {
                        name,
                        vartype,
                        rhs: Box::new(rhs),
                    })
                }

                // variable reassignment
                TokenKind::Identifier(_name) => {
                    // peek one ahead to see if it's '='
                    if let Some(Ok(next)) = self.peek_n(1) {
                        if matches!(next.kind, TokenKind::Assign) {
                            // consume identifier
                            let name =
                                match self.next_token().ok_or(CompilerError::UnexpectedEof)?? {
                                    tok @ Token {
                                        kind: TokenKind::Identifier(_),
                                        ..
                                    } => tok,
                                    _ => unreachable!(),
                                };

                            // consume '='
                            let _eq = self.next_token().ok_or(CompilerError::UnexpectedEof)??;

                            // parse RHS expression
                            let rhs = self.parse_expression()?;

                            self.expect_line_end()?;

                            return Ok(Ast::Reassign {
                                name,
                                rhs: Box::new(rhs),
                            });
                        }
                    }

                    let expr = self.parse_expression()?;
                    self.expect_line_end()?;

                    Ok(expr)
                }
                // bare expression statement
                _ => {
                    let expr = self.parse_expression()?;
                    self.expect_line_end()?;

                    Ok(expr)
                }
            }
        } else {
            Err(CompilerError::UnexpectedEof)
        }
    }

    fn parse_binary_op<F>(
        &mut self,
        operators: &[TokenKind],
        subparser: F,
    ) -> CompilerResult<'ip, Ast<'ip>>
    where
        F: Fn(&mut Self) -> CompilerResult<'ip, Ast<'ip>>,
    {
        let mut node = subparser(self)?;

        while let Some(Ok(tok)) =
            self.next_if(|tok| matches!(tok, x if operators.contains(&x.kind)))
        {
            node = Ast::BinaryOp {
                left: Box::new(node),
                op: tok,
                right: Box::new(subparser(self)?),
            };
        }

        Ok(node)
    }

    fn parse_expression(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_comparison()
    }

    fn parse_comparison(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(&[TokenKind::Eq, TokenKind::Neq], Self::parse_relational)
    }

    fn parse_relational(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(
            &[TokenKind::Gt, TokenKind::Gte, TokenKind::Lt, TokenKind::Lte],
            Self::parse_additive,
        )
    }

    fn parse_additive(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(
            &[TokenKind::Plus, TokenKind::Minus],
            Self::parse_multiplicative,
        )
    }

    fn parse_multiplicative(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(&[TokenKind::Star, TokenKind::Slash], Self::parse_atom)
    }

    fn parse_atom(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        let token = self.next_token().ok_or(CompilerError::UnexpectedEof)??;
        let node = match token.kind {
            TokenKind::Int(_) => Ast::Int(token),
            TokenKind::Identifier(_) => Ast::Identifier(token),
            TokenKind::Bool(_) => Ast::Bool(token),
            TokenKind::Minus | TokenKind::Plus | TokenKind::Not => Ast::UnaryOp {
                op: token,
                operand: Box::new(self.parse_atom()?),
            },
            TokenKind::Lparen => {
                let expr = self.parse_comparison()?;
                match self.next_token() {
                    Some(Ok(tok)) if matches!(tok.kind, TokenKind::Rparen) => expr,
                    Some(Ok(got)) => {
                        return Err(CompilerError::UnexpectedToken { got, expected: ")" })
                    }
                    _ => return Err(CompilerError::UnexpectedEof),
                }
            }
            _ => {
                return Err(CompilerError::UnexpectedToken {
                    got: token,
                    expected: "int, bool, identifier, unary operator, or '('",
                })
            }
        };
        Ok(node)
    }
}
