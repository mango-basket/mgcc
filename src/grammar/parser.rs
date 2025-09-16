use crate::{
    error::{CompilerError, CompilerResult},
    grammar::ast::Ast,
    tokenizer::{
        lexer::Lexer,
        token::{Keyword, Token, TokenKind},
    },
};
use std::{collections::VecDeque, iter::Peekable};

macro_rules! expect_match {
    // with explicit expected string
    ($parser:expr, $($pats:pat_param)|+ , $expected:expr) => {{
        let tok = $parser.next_token().ok_or(CompilerError::UnexpectedEof)??;
        if matches!(tok.kind, $($pats)|+) {
            Ok(tok)
        } else {
            Err(CompilerError::UnexpectedToken {
                got: tok,
                expected: $expected,
            })
        }
    }};

    // auto-generate expected (take first pattern only)
    ($parser:expr, $pat:pat_param $(| $rest:pat_param)*) => {{
        let tok = $parser.next_token().ok_or(CompilerError::UnexpectedEof)??;
        if matches!(tok.kind, $pat $(| $rest)*) {
            Ok(tok)
        } else {
            Err(CompilerError::UnexpectedToken {
                got: tok,
                expected: stringify!($pat), // fallback: pattern name
            })
        }
    }};
}

const PRECEDENCE: &[&[TokenKind]] = &[
    &[TokenKind::Or],
    &[TokenKind::And],
    &[TokenKind::Bor],
    &[TokenKind::Xor],
    &[TokenKind::Band],
    &[TokenKind::Eq, TokenKind::Neq],
    &[TokenKind::Gt, TokenKind::Gte, TokenKind::Lt, TokenKind::Lte],
    &[TokenKind::Shl, TokenKind::Shr],
    &[TokenKind::Plus, TokenKind::Minus],
    &[TokenKind::Star, TokenKind::Slash, TokenKind::Mod],
];

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

    fn consume_line_end(&mut self) -> CompilerResult<'ip, ()> {
        expect_match!(self, TokenKind::LineEnd)?;
        Ok(())
    }

    fn bump(&mut self) -> CompilerResult<'ip, Token<'ip>> {
        expect_match!(self, _)
    }

    fn peek_kind(&mut self) -> Option<TokenKind> {
        self.peek()
            .and_then(|r| r.as_ref().ok())
            .map(|t| t.kind.clone())
    }

    // -- Parse functions --

    pub fn parse(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.parse_items(None)
    }

    fn parse_items(
        &mut self,
        end: Option<TokenKind>, // pass EOF at top-level, RBrace in a block
    ) -> CompilerResult<'ip, Ast<'ip>> {
        let mut items = Vec::new();

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
                Some(Ok(tok)) if matches!(tok.kind, TokenKind::LineEnd) => {
                    self.consume_line_end()?
                }
                _ => items.push(self.parse_statement()?),
            }
        }

        Ok(Ast::Statements(items))
    }

    fn parse_item(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        if let Some(Ok(tok)) = self.peek() {
            match tok.kind {
                TokenKind::Keyword(Keyword::Fn) => {
                    // fn keyword
                    expect_match!(self, TokenKind::Keyword(Keyword::Fn))?;

                    // function name
                    let name = expect_match!(self, TokenKind::Identifier(_))?;

                    // parameters
                    expect_match!(self, TokenKind::Lparen)?;
                    let mut params = Vec::new();

                    while let Some(Ok(tok)) = self.peek() {
                        match tok.kind {
                            TokenKind::Identifier(_) => {
                                // param name
                                let pname = expect_match!(self, TokenKind::Identifier(_))?;
                                expect_match!(self, TokenKind::Colon)?;

                                // type
                                let ptype = self.parse_type()?;

                                params.push((pname, ptype));

                                // eat optional comma
                                if let Some(Ok(peek)) = self.peek() {
                                    if peek.kind == TokenKind::Comma {
                                        self.next_token(); // consume comma
                                    }
                                }
                            }
                            TokenKind::Rparen => break,
                            _ => {
                                return Err(CompilerError::UnexpectedToken {
                                    got: tok.clone(),
                                    expected: ")",
                                })
                            }
                        }
                    }

                    expect_match!(self, TokenKind::Rparen)?;

                    // optional return type
                    let mut ret = None;
                    if let Some(Ok(tok)) = self.peek() {
                        if tok.kind == TokenKind::Arrow {
                            expect_match!(self, TokenKind::Arrow)?;
                            let rtype = self.parse_type()?;
                            ret = Some(Box::new(rtype))
                        }
                    }

                    // function body
                    let body = self.parse_statements()?; // you probably have parse_block

                    return Ok(Ast::Func {
                        name,
                        params,
                        ret,
                        body: Box::new(body),
                    });
                }
                _ => {
                    return Err(CompilerError::UnexpectedToken {
                        got: tok.clone(),
                        expected: "",
                    });
                }
            }
        }
        Err(CompilerError::UnexpectedEof)
    }

    fn parse_statements(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        let mut stmts = Vec::new();

        loop {
            match self.peek() {
                None => return Err(CompilerError::UnexpectedEof),
                Some(Ok(tok)) if tok.clone().kind == TokenKind::Rbrace => break, // stop at `}`
                Some(Ok(tok)) if matches!(tok.kind, TokenKind::LineEnd) => {
                    self.consume_line_end()?
                }
                _ => stmts.push(self.parse_statement()?),
            }
        }

        Ok(Ast::Statements(stmts))
    }

    fn parse_type(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        if let Some(Ok(tok)) = self.peek() {
            match &tok.kind {
                TokenKind::Ref => {
                    let _ = self.next_token();
                    let inner = self.parse_type()?;
                    Ok(Ast::Ref(Box::new(inner)))
                }
                TokenKind::Identifier(_) => {
                    let ident = expect_match!(self, TokenKind::Identifier(_))?;
                    Ok(Ast::Identifier(ident))
                }
                _ => Err(CompilerError::UnexpectedToken {
                    got: tok.clone(),
                    expected: "type identifier",
                }),
            }
        } else {
            Err(CompilerError::UnexpectedEof)
        }
    }

    fn parse_vardef(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.bump()?; // consume var keyword
        let name = expect_match!(self, TokenKind::Identifier(_))?;

        // look ahead for optional colon
        let mut vartype = None;
        if let Some(Ok(next)) = self.peek() {
            if matches!(next.kind, TokenKind::Colon) {
                let _ = self.next_token();
                let t = self.parse_type()?;
                vartype = Some(Box::new(t))
            }
        }
        expect_match!(self, TokenKind::Assign)?;

        let rhs = self.parse_expression()?;
        self.consume_line_end()?;

        Ok(Ast::VarDef {
            name,
            vartype,
            rhs: Box::new(rhs),
        })
    }

    fn parse_reassign(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        let lhs = self.parse_unary()?;

        if let Some(Ok(next)) = self.peek() {
            if matches!(next.kind, TokenKind::Assign) {
                self.bump()?; // eq token
                let rhs = self.parse_expression()?;
                self.consume_line_end()?;
                return Ok(Ast::Reassign {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                });
            }
        }

        self.consume_line_end()?;
        Ok(lhs)
    }

    fn parse_break_stmt(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.bump()?;

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

        self.consume_line_end()?;
        Ok(Ast::Break(expr))
    }

    fn parse_ret_stmt(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        self.bump()?;

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

        self.consume_line_end()?;
        Ok(Ast::Return(expr))
    }

    fn parse_statement(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        if let Some(kind) = self.peek_kind() {
            match kind {
                TokenKind::Keyword(Keyword::Var) => self.parse_vardef(),
                TokenKind::Keyword(Keyword::Disp) => {
                    self.bump()?;
                    Ok(Ast::Disp(Box::new(self.parse_expression()?)))
                }
                TokenKind::Identifier(_) | TokenKind::Star => self.parse_reassign(),
                TokenKind::Keyword(Keyword::Break) => self.parse_break_stmt(),
                TokenKind::Keyword(Keyword::Return) => self.parse_ret_stmt(),
                TokenKind::Keyword(Keyword::Continue) => {
                    self.bump()?;
                    self.consume_line_end()?;
                    Ok(Ast::Continue)
                }

                // If its a line end, skip that and get a new statement (for cases when newlinw
                // follows { )
                TokenKind::LineEnd => {
                    self.consume_line_end()?;
                    Ok(self.parse_statement()?)
                }

                // bare expression statement
                _ => {
                    let expr = self.parse_expression()?;
                    self.consume_line_end()?;

                    Ok(expr)
                }
            }
        } else {
            Err(CompilerError::UnexpectedEof)
        }
    }

    fn parse_expression(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        fn parse_level<'ip>(
            parser: &mut Parser<'ip>,
            table: &[&[TokenKind]],
            index: usize,
        ) -> CompilerResult<'ip, Ast<'ip>> {
            if index >= table.len() {
                return parser.parse_unary(); // bottom-most fallback
            }

            parser.parse_binary_op(table[index], |p| parse_level(p, table, index + 1))
        }

        parse_level(self, PRECEDENCE, 0)
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

    fn parse_unary(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        // Peek to see if next token is a unary operator (without consuming it)
        if let Some(kind) = self.peek_kind() {
            match kind {
                TokenKind::Minus | TokenKind::Plus | TokenKind::Not | TokenKind::Bnot => {
                    let op = self.next_token().ok_or(CompilerError::UnexpectedEof)??;
                    let operand = self.parse_unary()?;
                    return Ok(Ast::UnaryOp {
                        op,
                        operand: Box::new(operand),
                    });
                }
                TokenKind::Star => {
                    let _ = self.next_token().ok_or(CompilerError::UnexpectedEof)??;
                    let operand = self.parse_unary()?;
                    return Ok(Ast::Deref(Box::new(operand)));
                }
                _ => {}
            }
        }

        // Fallback
        self.parse_ref()
    }

    fn parse_ref(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        if let Some(Ok(toke_ref)) = self.peek() {
            if matches!(toke_ref.kind, TokenKind::Ref) {
                self.bump()?;
                let operand = self.parse_ref()?;
                return Ok(Ast::Ref(Box::new(operand)));
            }
        }

        self.parse_atom()
    }

    fn parse_atom(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        let token = self.bump()?;

        match token.kind {
            TokenKind::Int(_) => Ok(Ast::Int(token)),
            TokenKind::Bool(_) => Ok(Ast::Bool(token)),
            TokenKind::Identifier(_) => self.parse_func_call(&token),

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

    fn parse_func_call(&mut self, token: &Token<'ip>) -> Result<Ast<'ip>, CompilerError<'ip>> {
        if let Some(kind) = self.peek_kind() {
            if !matches!(kind, TokenKind::Lparen) {
                return Ok(Ast::Identifier(token.clone()));
            }

            self.bump()?;

            let mut params = Vec::new();

            while let Some(Ok(tok)) = self.peek() {
                match tok.kind {
                    TokenKind::Identifier(_) => {
                        // param name
                        let pname = expect_match!(self, TokenKind::Identifier(_))?;
                        expect_match!(self, TokenKind::Colon)?;

                        // type
                        let ptype = self.parse_type()?;

                        params.push((pname, ptype));

                        // eat optional comma
                        if let Some(Ok(peek)) = self.peek() {
                            if peek.kind == TokenKind::Comma {
                                self.next_token(); // consume comma
                            }
                        }
                    }
                    TokenKind::Rparen => break,
                    _ => {
                        return Err(CompilerError::UnexpectedToken {
                            got: tok.clone(),
                            expected: ")",
                        })
                    }
                }
            }

            expect_match!(self, TokenKind::Rparen)?;

            Ok(Ast::FuncCall {
                name: token.clone(),
                params,
            })
        } else {
            Ok(Ast::Identifier(token.clone()))
        }
    }

    fn parse_if_expr(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        // parse condition
        let condition = self.parse_expression()?;

        // parse if-body block
        expect_match!(self, TokenKind::Lbrace)?;
        let ifbody = self.parse_items(Some(TokenKind::Rbrace))?;
        expect_match!(self, TokenKind::Rbrace)?;

        // parse optional else / else if chain
        let elsebody = if let Some(_) =
            self.next_if(|tok| matches!(tok.kind, TokenKind::Keyword(Keyword::Else)))
        {
            if let Some(Ok(peek)) = self.peek() {
                if matches!(peek.kind, TokenKind::LineEnd) {
                    self.consume_line_end()?;
                }
            }

            if let Some(Ok(peek)) = self.peek() {
                if matches!(peek.kind, TokenKind::Keyword(Keyword::If)) {
                    self.next_token(); // consume 'if'
                    Some(Box::new(self.parse_if_expr()?))
                } else {
                    expect_match!(self, TokenKind::Lbrace)?;
                    let else_stmts = self.parse_items(Some(TokenKind::Rbrace))?;
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
        let body = self.parse_items(Some(TokenKind::Rbrace))?;
        expect_match!(self, TokenKind::Rbrace)?;
        Ok(Ast::Loop(Box::new(body)))
    }
}
