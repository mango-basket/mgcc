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
    VarDef {
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
    Loop(Box<Ast<'ip>>),
    Continue,
    Break(Option<Box<Ast<'ip>>>),
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

                    Ok(Ast::VarDef {
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

                // Loops
                TokenKind::Keyword(Keyword::Continue) => {
                    expect_match!(self, TokenKind::Keyword(Keyword::Continue))?;
                    expect_match!(self, TokenKind::LineEnd)?;
                    Ok(Ast::Continue)
                }
                TokenKind::Keyword(Keyword::Break) => {
                    expect_match!(self, TokenKind::Keyword(Keyword::Break))?;

                    let expr = if !matches!(
                        self.peek(),
                        Some(Ok(Token {
                            kind: TokenKind::LineEnd,
                            ..
                        }))
                    ) {
                        Some(Box::new(self.parse_expression()?))
                    } else {
                        None
                    };

                    expect_match!(self, TokenKind::LineEnd)?;
                    Ok(Ast::Break(expr))
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
        self.parse_logic_or()
    }

    fn parse_if_expr(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        // parse condition
        let condition = self.parse_expression()?;

        // parse if-body block
        expect_match!(self, TokenKind::Lbrace)?;
        let ifbody = self.parse_statements(Some(TokenKind::Rbrace))?;
        expect_match!(self, TokenKind::Rbrace)?;

        // parse optional else / else if chain
        let elsebody = if let Some(_) =
            self.next_if(|tok| matches!(tok.kind, TokenKind::Keyword(Keyword::Else)))
        {
            // skip any line ends between else and next token
            while matches!(
                self.peek(),
                Some(Ok(Token {
                    kind: TokenKind::LineEnd,
                    ..
                }))
            ) {
                self.next_token();
            }

            if let Some(Ok(peek)) = self.peek() {
                if matches!(peek.kind, TokenKind::Keyword(Keyword::If)) {
                    self.next_token(); // consume 'if'
                                       // recursively parse nested if, but flatten in the AST
                    Some(Box::new(self.parse_if_expr()?))
                } else {
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
    }

    fn parse_loop_expr(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        expect_match!(self, TokenKind::Lbrace)?;
        let body = self.parse_statements(Some(TokenKind::Rbrace))?;
        expect_match!(self, TokenKind::Rbrace)?;
        Ok(Ast::Loop(Box::new(body)))
    }

    fn parse_logic_or(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(&[TokenKind::Or], Self::parse_logic_and)
    }

    fn parse_logic_and(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(&[TokenKind::And], Self::parse_bit_or)
    }

    fn parse_bit_or(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(&[TokenKind::Bor], Self::parse_bit_xor)
    }

    fn parse_bit_xor(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(&[TokenKind::Xor], Self::parse_bit_and)
    }

    fn parse_bit_and(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(&[TokenKind::Band], Self::parse_equality)
    }

    fn parse_equality(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(&[TokenKind::Eq, TokenKind::Neq], Self::parse_relational)
    }

    fn parse_relational(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(
            &[TokenKind::Gt, TokenKind::Gte, TokenKind::Lt, TokenKind::Lte],
            Self::parse_bit_shift,
        )
    }

    fn parse_bit_shift(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(&[TokenKind::Shl, TokenKind::Shr], Self::parse_additive)
    }

    fn parse_additive(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(
            &[TokenKind::Plus, TokenKind::Minus],
            Self::parse_multiplicative,
        )
    }

    fn parse_multiplicative(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_binary_op(&[TokenKind::Star, TokenKind::Slash], Self::parse_unary)
    }

    fn parse_unary(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        // Peek to see if next token is a unary operator (without consuming it)
        if let Some(Ok(tok_ref)) = self.peek() {
            if matches!(
                tok_ref.kind,
                TokenKind::Minus | TokenKind::Plus | TokenKind::Not | TokenKind::Bnot
            ) {
                // consume the operator and get the owned Token
                let op = self.next_token().ok_or(CompilerError::UnexpectedEof)??;
                // recurse so unary is right-associative: `! - x` etc.
                let operand = self.parse_unary()?;
                return Ok(Ast::UnaryOp {
                    op,
                    operand: Box::new(operand),
                });
            }
        }

        // not a unary operator -> delegate to atom
        self.parse_atom()
    }

    fn parse_atom(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        let token = self.next_token().ok_or(CompilerError::UnexpectedEof)??;

        match token.kind {
            TokenKind::Int(_) => Ok(Ast::Int(token)),
            TokenKind::Bool(_) => Ok(Ast::Bool(token)),
            TokenKind::Identifier(_) => Ok(Ast::Identifier(token)),

            TokenKind::Lparen => {
                let expr = self.parse_expression()?;
                expect_match!(self, TokenKind::Rparen)?;
                Ok(expr)
            }

            // if/loop are parsed as atoms (token already consumed)
            TokenKind::Keyword(Keyword::If) => self.parse_if_expr(),
            TokenKind::Keyword(Keyword::Loop) => self.parse_loop_expr(),

            _ => Err(CompilerError::UnexpectedToken {
                got: token,
                expected: "int, bool, identifier, unary operator, if, loop or '('",
            }),
        }
    }
}
