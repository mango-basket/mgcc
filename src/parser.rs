use std::{collections::VecDeque, iter::Peekable};

use crate::{
    error::{CompilerError, CompilerResult},
    lexer::{Keyword, Lexer, Token, TokenKind},
};

macro_rules! expect_match {
    // with explicit expected
    ($parser:expr, $($pats:pat_param)|+ , $expected:expr) => {{
        let tok = $parser.next_token().ok_or(CompilerError::UnexpectedEof)??;
        if matches!(tok.kind, $($pats)|+) {
            Ok(tok)
        } else {
            Err(CompilerError::UnexpectedToken { got: tok, expected: $expected })
        }
    }};

    // auto-generate expected
    ($parser:expr, $($pats:pat_param)|+) => {{
        let tok = $parser.next_token().ok_or(CompilerError::UnexpectedEof)??;
        if matches!(tok.kind, $($pats)|+) {
            Ok(tok)
        } else {
            Err(CompilerError::UnexpectedToken {
                got: tok.clone(),
                expected: tok.kind.expected_name(), // <- call it on the actual token
            })
        }
    }};
}

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
    IfElse {
        condition: Box<Ast<'ip>>,
        ifbody: Box<Ast<'ip>>,
        elsebody: Option<Box<Ast<'ip>>>,
    },
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

    // -- Parse functions --

    pub fn parse(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_statements(None)
    }

    fn parse_statements(
        &mut self,
        end: Option<TokenKind>, // pass EOF at top-level, RBrace in a block
    ) -> CompilerResult<'ip, Ast<'ip>> {
        let mut stmts = Vec::new();

        loop {
            match self.peek() {
                None => {
                    if end.is_none() {
                        break; // hit eof at top-level
                    } else {
                        return Err(CompilerError::UnexpectedEof);
                    }
                }
                Some(Ok(tok)) if Some(tok.clone().kind) == end => break, // stop at `}`
                _ => stmts.push(Box::new(self.parse_statement()?)),
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

                    let name = expect_match!(self, TokenKind::Identifier(_))?;

                    // look ahead for optional colon
                    let mut vartype = None;
                    if let Some(Ok(next)) = self.peek() {
                        if matches!(next.kind, TokenKind::Colon) {
                            let _ = self.next_token();

                            let t =
                                expect_match!(self, TokenKind::Identifier(_), "type identifier")?;

                            vartype = Some(t)
                        }
                    }
                    expect_match!(self, TokenKind::Assign)?;

                    let rhs = self.parse_expression()?;
                    expect_match!(self, TokenKind::LineEnd)?;

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
                            let name = self.next_token().ok_or(CompilerError::UnexpectedEof)??;

                            // consume '='
                            let _eq = self.next_token().ok_or(CompilerError::UnexpectedEof)??;

                            // parse RHS expression
                            let rhs = self.parse_expression()?;

                            expect_match!(self, TokenKind::LineEnd)?;

                            return Ok(Ast::Reassign {
                                name,
                                rhs: Box::new(rhs),
                            });
                        }
                    }

                    let expr = self.parse_expression()?;
                    expect_match!(self, TokenKind::LineEnd)?;

                    Ok(expr)
                }
                // If its a line end, skip that and get a new statement (for cases when newlinw
                // follows { )
                TokenKind::LineEnd => {
                    let _ = self.next_token().ok_or(CompilerError::UnexpectedEof)??;
                    Ok(self.parse_statement()?)
                }

                // bare expression statement
                _ => {
                    let expr = self.parse_expression()?;
                    expect_match!(self, TokenKind::LineEnd)?;

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
        self.parse_if_expr()
    }

    fn parse_if_expr(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        if let Some(Ok(_if_tok)) =
            self.next_if(|tok| matches!(tok.kind, TokenKind::Keyword(Keyword::If)))
        {
            // parse condition
            let condition = self.parse_comparison()?;

            // expect '{'
            expect_match!(self, TokenKind::Lbrace)?;

            // parse if-body
            let ifbody = self.parse_statements(Some(TokenKind::Rbrace))?;

            // expect '}'
            expect_match!(self, TokenKind::Rbrace)?;

            // check for "else"
            let elsebody = if let Some(Ok(_tok)) =
                self.next_if(|tok| matches!(tok.kind, TokenKind::Keyword(Keyword::Else)))
            {
                // is it "else if ..." ?
                if let Some(Ok(peek)) = self.peek() {
                    if matches!(peek.kind, TokenKind::Keyword(Keyword::If)) {
                        // recursively parse another if-expression
                        Some(Box::new(self.parse_if_expr()?))
                    } else {
                        // plain else, expect '{'
                        expect_match!(self, TokenKind::Lbrace)?;

                        let else_stmts = self.parse_statements(Some(TokenKind::Rbrace))?;

                        expect_match!(self, TokenKind::Rbrace)?;

                        Some(Box::new(else_stmts))
                    }
                } else {
                    None
                }
            } else {
                None
            };

            Ok(Ast::IfElse {
                condition: Box::new(condition),
                ifbody: Box::new(ifbody),
                elsebody,
            })
        } else {
            self.parse_comparison()
        }
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
