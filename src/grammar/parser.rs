use crate::{
    error::{CompilerError, CompilerResult},
    grammar::ast::{AstKind, AstNode},
    tokenizer::{
        lexer::Lexer,
        token::{Keyword, Span, Token, TokenKind},
    },
};
use std::{collections::VecDeque, iter::Peekable};

macro_rules! expect_match {
    // with explicit expected string
    ($parser:expr, $($pats:pat_param)|+ , $expected:expr) => {{
        let tok = $parser.next().ok_or(CompilerError::UnexpectedEof)??;
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
        let tok = $parser.next().ok_or(CompilerError::UnexpectedEof)??;
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
    pos: isize,
    slice_stack: Vec<usize>,
    input: &'ip str,
}

impl<'ip> Parser<'ip> {
    pub fn new(lexer: Lexer<'ip>, input: &'ip str) -> Self {
        Self {
            lexer: lexer.peekable(),
            buffer: VecDeque::new(),
            slice_stack: Vec::new(),
            pos: -1,
            input,
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

    pub fn start_span(&mut self) -> CompilerResult<'ip, ()> {
        if let Some(Ok(tok)) = self.peek().cloned() {
            self.slice_stack.push(tok.span.start);
        }

        Ok(())
    }

    pub fn gen_node(&mut self, kind: AstKind<'ip>) -> AstNode<'ip> {
        let start = self.slice_stack.pop().expect("slice stack is empty");
        let end = self.pos as usize;
        AstNode::new(kind, Span::new(start, end, self.input))
    }

    pub fn next(&mut self) -> Option<CompilerResult<'ip, Token<'ip>>> {
        if let Some(tok) = self.buffer.pop_front() {
            if let Ok(tok) = &tok {
                self.pos = tok.span.end as isize;
            }
            Some(tok)
        } else if let Some(tok) = self.lexer.next() {
            if let Ok(tok) = &tok {
                self.pos = tok.span.end as isize;
            }
            Some(tok)
        } else {
            None
        }
    }

    pub fn next_if<F>(&mut self, f: F) -> Option<CompilerResult<'ip, Token<'ip>>>
    where
        F: Fn(&Token<'ip>) -> bool,
    {
        match self.peek() {
            Some(Ok(tok)) if f(tok) => self.next(),
            _ => None,
        }
    }

    pub fn peek(&mut self) -> Option<&CompilerResult<'ip, Token<'ip>>> {
        self.peek_n(0)
    }

    pub fn expected_peek(&mut self) -> CompilerResult<'ip, Token<'ip>> {
        self.peek().ok_or(CompilerError::UnexpectedEof).cloned()?
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

    pub fn parse(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        self.parse_items(None)
    }

    fn parse_items(
        &mut self,
        end: Option<TokenKind>, // pass EOF at top-level, RBrace in a block
    ) -> CompilerResult<'ip, AstNode<'ip>> {
        self.start_span()?;
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
                _ => items.push(self.parse_item()?),
            }
        }

        Ok(self.gen_node(AstKind::Items(items)))
    }

    fn parse_item(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        self.start_span()?;
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

                    if !matches!(self.peek_kind(), Some(TokenKind::Rparen)) {
                        loop {
                            // param name
                            let pname = expect_match!(self, TokenKind::Identifier(_))?;
                            expect_match!(self, TokenKind::Colon)?;

                            // type
                            let ptype = self.parse_type()?;
                            params.push((pname, ptype));

                            match self.peek_kind() {
                                Some(TokenKind::Comma) => {
                                    self.bump()?; // consume comma

                                    // if next is ')', that's trailing comma → break
                                    if matches!(self.peek_kind(), Some(TokenKind::Rparen)) {
                                        break;
                                    }
                                }
                                _ => break,
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

                    expect_match!(self, TokenKind::Lbrace)?;

                    // function body
                    let body = self.parse_statements()?; // or parse_block

                    expect_match!(self, TokenKind::Rbrace)?;

                    return Ok(self.gen_node(AstKind::Func {
                        name,
                        params,
                        ret,
                        body: Box::new(body),
                    }));
                }
                _ => {
                    return Err(CompilerError::UnexpectedToken {
                        got: tok.clone(),
                        expected: "fn",
                    });
                }
            }
        }
        Err(CompilerError::UnexpectedEof)
    }

    fn parse_statements(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        self.start_span()?;
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

        Ok(self.gen_node(AstKind::Statements(stmts)))
    }

    fn parse_type(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        self.start_span()?;
        if let Some(Ok(tok)) = self.peek() {
            match &tok.kind {
                TokenKind::Ref => {
                    self.bump()?;
                    let inner = self.parse_type()?;
                    Ok(self.gen_node(AstKind::Ref(Box::new(inner))))
                }
                TokenKind::Identifier(_) => {
                    let ident = expect_match!(self, TokenKind::Identifier(_))?;
                    Ok(self.gen_node(AstKind::Identifier(ident.kind.clone())))
                }
                TokenKind::Lsquare => {
                    self.bump()?;

                    let size = if matches!(self.expected_peek()?.kind, TokenKind::Int(_)) {
                        let size = expect_match!(self, TokenKind::Int(_))?;
                        expect_match!(self, TokenKind::Colon)?;
                        Some(size)
                    } else {
                        None
                    };

                    let inner = self.parse_type()?;
                    expect_match!(self, TokenKind::Rsquare)?;
                    Ok(self.gen_node(AstKind::ArrayDef {
                        size,
                        ty: Box::new(inner),
                    }))
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

    fn parse_vardef(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        self.start_span()?;
        self.bump()?; // consume var keyword

        let name = expect_match!(self, TokenKind::Identifier(_))?;

        // look ahead for optional colon
        let mut vartype = None;
        if let Some(Ok(next)) = self.peek() {
            if matches!(next.kind, TokenKind::Colon) {
                let _ = self.next();
                let t = self.parse_type()?;
                vartype = Some(Box::new(t))
            }
        }

        // arraydef syntax or normal assign
        let rhs = match expect_match!(
            self,
            TokenKind::Assign | TokenKind::Lsquare,
            "variable assignment"
        )?
        .kind
        {
            TokenKind::Assign => {
                let rhs = self.parse_expression()?;
                rhs
            }
            TokenKind::Lsquare => {
                self.start_span()?;
                let size = expect_match!(self, TokenKind::Int(_))?;
                expect_match!(self, TokenKind::Colon)?;
                let ty = self.parse_type()?;
                expect_match!(self, TokenKind::Rsquare)?;
                self.gen_node(AstKind::ArrayDef {
                    size: Some(size),
                    ty: Box::new(ty),
                })
            }
            _ => unreachable!(),
        };
        self.consume_line_end()?;

        Ok(self.gen_node(AstKind::VarDef {
            name,
            vartype,
            rhs: Box::new(rhs),
        }))
    }

    fn parse_reassign(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        self.start_span()?;
        let lhs = self.parse_unary()?;

        if let Some(Ok(next)) = self.peek() {
            if matches!(next.kind, TokenKind::Assign) {
                self.bump()?; // eq token
                let rhs = self.parse_expression()?;
                self.consume_line_end()?;
                return Ok(self.gen_node(AstKind::Reassign {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }));
            }
        }

        self.consume_line_end()?;
        Ok(lhs)
    }

    fn parse_break_stmt(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        self.start_span()?;
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
        Ok(self.gen_node(AstKind::Break(expr)))
    }

    fn parse_ret_stmt(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        self.start_span()?;
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
        Ok(self.gen_node(AstKind::Return(expr)))
    }

    fn parse_statement(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        self.start_span()?;
        if let Some(kind) = self.peek_kind() {
            match kind {
                TokenKind::Keyword(Keyword::Var) => self.parse_vardef(),
                TokenKind::Keyword(Keyword::Disp) => {
                    self.bump()?;
                    let expr = self.parse_expression()?;
                    Ok(self.gen_node(AstKind::Disp(Box::new(expr))))
                }
                TokenKind::Identifier(_) | TokenKind::Star => self.parse_reassign(),
                TokenKind::Keyword(Keyword::Breakpoint) => {
                    self.bump()?;
                    self.consume_line_end()?;
                    Ok(self.gen_node(AstKind::Breakpoint))
                }
                TokenKind::Keyword(Keyword::Break) => self.parse_break_stmt(),
                TokenKind::Keyword(Keyword::Return) => self.parse_ret_stmt(),
                TokenKind::Keyword(Keyword::Continue) => {
                    self.bump()?;
                    self.consume_line_end()?;
                    Ok(self.gen_node(AstKind::Continue))
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

    fn parse_expression(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        fn parse_level<'ip>(
            parser: &mut Parser<'ip>,
            table: &[&[TokenKind]],
            index: usize,
        ) -> CompilerResult<'ip, AstNode<'ip>> {
            if index >= table.len() {
                return parser.parse_as(); // bottom-most fallback
            }

            parser.parse_binary_op(table[index], |p| parse_level(p, table, index + 1))
        }

        parse_level(self, PRECEDENCE, 0)
    }

    fn parse_binary_op<F>(
        &mut self,
        operators: &[TokenKind],
        subparser: F,
    ) -> CompilerResult<'ip, AstNode<'ip>>
    where
        F: Fn(&mut Self) -> CompilerResult<'ip, AstNode<'ip>>,
    {
        self.start_span()?;
        let mut node = subparser(self)?;

        while let Some(Ok(tok)) =
            self.next_if(|tok| matches!(tok, x if operators.contains(&x.kind)))
        {
            let sub = subparser(self)?;
            node = self.gen_node(AstKind::BinaryOp {
                left: Box::new(node),
                op: tok,
                right: Box::new(sub),
            });
        }

        Ok(node)
    }

    fn parse_as(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        // unary ("as" ident)+
        self.start_span()?;

        let mut node = self.parse_unary()?;

        while let Some(Ok(_)) =
            self.next_if(|tok| matches!(tok.kind, TokenKind::Keyword(Keyword::As)))
        {
            // get an identifier
            let ty = expect_match!(self, TokenKind::Identifier(_))?;
            node = self.gen_node(AstKind::As {
                lhs: Box::new(node),
                rhs: ty,
            })
        }

        Ok(node)
    }

    fn parse_unary(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        // Peek to see if next token is a unary operator (without consuming it)
        if let Some(kind) = self.peek_kind() {
            match kind {
                TokenKind::Minus | TokenKind::Plus | TokenKind::Not | TokenKind::Bnot => {
                    self.start_span()?;
                    let op = self.next().ok_or(CompilerError::UnexpectedEof)??;
                    let operand = self.parse_unary()?;
                    return Ok(self.gen_node(AstKind::UnaryOp {
                        op,
                        operand: Box::new(operand),
                    }));
                }
                TokenKind::Star => {
                    self.start_span()?;
                    let _ = self.next().ok_or(CompilerError::UnexpectedEof)??;
                    let operand = self.parse_unary()?;
                    return Ok(self.gen_node(AstKind::Deref(Box::new(operand))));
                }
                _ => {}
            }
        }

        // Fallback
        self.parse_index()
    }

    fn parse_index(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        self.start_span()?;

        let mut node = self.parse_ref()?;

        while let Some(Ok(_)) = self.next_if(|tok| matches!(tok.kind, TokenKind::Lsquare)) {
            // get an identifier
            let index = self.parse_expression()?;
            expect_match!(self, TokenKind::Rsquare)?;

            node = self.gen_node(AstKind::Index {
                lhs: Box::new(node),
                rhs: Box::new(index),
            })
        }

        Ok(node)
    }

    fn parse_ref(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        if let Some(Ok(toke_ref)) = self.peek() {
            if matches!(toke_ref.kind, TokenKind::Ref) {
                self.start_span()?;
                self.bump()?;
                let operand = self.parse_ref()?;
                return Ok(self.gen_node(AstKind::Ref(Box::new(operand))));
            }
        }

        self.parse_atom()
    }

    fn parse_atom(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        self.start_span()?;
        let token = self.bump()?;

        match token.kind {
            TokenKind::Int(_) => Ok(self.gen_node(AstKind::Int(token.kind))),
            TokenKind::Bool(_) => Ok(self.gen_node(AstKind::Bool(token.kind))),
            TokenKind::Char(_) => Ok(self.gen_node(AstKind::Char(token.kind))),
            TokenKind::String(_) => Ok(self.gen_node(AstKind::String(token.kind))),
            TokenKind::Identifier(_) => self.parse_func_call(&token),

            // Arrays
            TokenKind::Lsquare => self.parse_array(),

            TokenKind::Lparen => {
                let expr = self.parse_expression()?;

                // pop off excess slice
                self.slice_stack.pop().expect("slice stack is empty");

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

    fn parse_func_call(&mut self, token: &Token<'ip>) -> Result<AstNode<'ip>, CompilerError<'ip>> {
        // slice already started in atom
        if let Some(TokenKind::Lparen) = self.peek_kind() {
            self.bump()?; // consume '('

            let mut args = Vec::new();

            if !matches!(self.peek_kind(), Some(TokenKind::Rparen)) {
                loop {
                    let expr = self.parse_expression()?;
                    args.push(expr);

                    match self.peek_kind() {
                        Some(TokenKind::Comma) => {
                            self.bump()?; // consume comma

                            // if next is ')', that's trailing comma  break
                            if matches!(self.peek_kind(), Some(TokenKind::Rparen)) {
                                break;
                            }
                        }
                        _ => break,
                    }
                }
            }

            expect_match!(self, TokenKind::Rparen)?;

            Ok(self.gen_node(AstKind::FuncCall {
                name: token.clone(),
                args,
            }))
        } else {
            Ok(self.gen_node(AstKind::Identifier(token.kind.clone())))
        }
    }

    fn parse_if_expr(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        // slice already started in atom

        // parse condition
        let condition = self.parse_expression()?;

        // parse if-body block
        expect_match!(self, TokenKind::Lbrace)?;
        let ifbody = self.parse_statements()?;
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
                    self.next(); // consume 'if'
                    Some(Box::new(self.parse_if_expr()?))
                } else {
                    expect_match!(self, TokenKind::Lbrace)?;
                    let else_stmts = self.parse_statements()?;
                    expect_match!(self, TokenKind::Rbrace)?;
                    Some(Box::new(else_stmts))
                }
            } else {
                None
            }
        } else {
            None
        };

        Ok(self.gen_node(AstKind::IfElse {
            condition: Box::new(condition),
            ifbody: Box::new(ifbody),
            elsebody,
        }))
    }

    fn parse_loop_expr(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        // slice already started in atom

        expect_match!(self, TokenKind::Lbrace)?;
        let body = self.parse_statements()?;
        expect_match!(self, TokenKind::Rbrace)?;
        Ok(self.gen_node(AstKind::Loop(Box::new(body))))
    }

    fn parse_array(&mut self) -> CompilerResult<'ip, AstNode<'ip>> {
        // slice started in atom
        // [ already consumed
        let mut elems = Vec::new();
        if !matches!(self.peek_kind(), Some(TokenKind::Rsquare)) {
            loop {
                let expr = self.parse_expression()?;
                elems.push(expr);

                match self.peek_kind() {
                    Some(TokenKind::Comma) => {
                        self.bump()?; // consume comma

                        // if next is ')', that's trailing comma  break
                        if matches!(self.peek_kind(), Some(TokenKind::Rparen)) {
                            break;
                        }
                    }
                    _ => break,
                }
            }
        }

        expect_match!(self, TokenKind::Rsquare)?;

        if elems.len() == 0 {
            return Err(CompilerError::Semantic {
                err: "zero-length arrays are not allowed".into(),
                span: Span {
                    start: self.slice_stack.pop().unwrap(),
                    end: self.pos as usize,
                    input: self.input,
                },
            });
        }

        Ok(self.gen_node(AstKind::Array(elems)))
    }
}
