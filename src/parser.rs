use std::{collections::VecDeque, iter::Peekable};

use crate::{
    error::{CompilerError, CompilerResult},
    lexer::{Keyword, Lexer, Slice, Token, TokenKind},
};

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

#[derive(Debug)]
pub enum Ast<'ip> {
    Identifier(Token<'ip>),
    Int(Token<'ip>),
    Bool(Token<'ip>),
    Ref(Box<Ast<'ip>>),
    Deref(Box<Ast<'ip>>),
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
        vartype: Option<Box<Ast<'ip>>>,
        rhs: Box<Ast<'ip>>,
    },
    Reassign {
        lhs: Box<Ast<'ip>>,
        rhs: Box<Ast<'ip>>,
    },
    Statements(Vec<Box<Ast<'ip>>>),
    IfElse {
        condition: Box<Ast<'ip>>,
        ifbody: Box<Ast<'ip>>,
        elsebody: Option<Box<Ast<'ip>>>,
    },
    Loop(Box<Ast<'ip>>),
    Break(Option<Box<Ast<'ip>>>),
    Continue,
    Disp(Box<Ast<'ip>>),
}

impl<'ip> Ast<'ip> {
    pub fn pretty(&self, indent: usize) -> String {
        let pad = "  ".repeat(indent);
        match self {
            Ast::Identifier(tok) => format!("{}Ident({})", pad, tok.slice.get_str()),
            Ast::Int(tok) => format!("{}Int({})", pad, tok.slice.get_str()),
            Ast::Bool(tok) => format!("{}Bool({})", pad, tok.slice.get_str()),
            Ast::Ref(inner) => format!("{}Ref({})", pad, inner.pretty(0)),
            Ast::Deref(inner) => format!("{}Deref({})", pad, inner.pretty(0)),
            Ast::UnaryOp { op, operand } => {
                format!(
                    "{}UnaryOp({},{})",
                    pad,
                    op.slice.get_str(),
                    operand.pretty(0)
                )
            }
            Ast::BinaryOp { left, op, right } => {
                format!(
                    "{}BinaryOp({},{},{})",
                    pad,
                    op.slice.get_str(),
                    left.pretty(0),
                    right.pretty(0)
                )
            }
            Ast::VarDef { name, vartype, rhs } => {
                if let Some(t) = vartype {
                    format!(
                        "{}VarDef({}:{},{})",
                        pad,
                        name.slice.get_str(),
                        t.pretty(0),
                        rhs.pretty(0)
                    )
                } else {
                    format!("{}VarDef({},{})", pad, name.slice.get_str(), rhs.pretty(0))
                }
            }
            Ast::Reassign { lhs, rhs } => {
                format!("{}Reassign({}, {})", pad, lhs.pretty(0), rhs.pretty(0))
            }
            Ast::Statements(stmts) => {
                let mut s = format!("{}Statements", pad);
                for stmt in stmts {
                    s.push('\n');
                    s.push_str(&stmt.pretty(indent + 1));
                }
                s
            }
            Ast::IfElse {
                condition,
                ifbody,
                elsebody,
            } => {
                let else_str = if let Some(e) = elsebody {
                    format!(", Else({})", e.pretty(0))
                } else {
                    "".to_string()
                };
                format!(
                    "{}If({},{}){}",
                    pad,
                    condition.pretty(0),
                    ifbody.pretty(0),
                    else_str
                )
            }
            Ast::Loop(body) => format!("{}Loop({})", pad, body.pretty(0)),
            Ast::Break(expr_opt) => {
                if let Some(expr) = expr_opt {
                    format!("{}Break({})", pad, expr.pretty(0))
                } else {
                    format!("{}Break", pad)
                }
            }
            Ast::Continue => format!("{}Continue", pad),
            Ast::Disp(ast) => format!("{}Disp {}", pad, ast.pretty(0)),
        }
    }

    pub fn get_slice(&self) -> Slice<'ip> {
        match self {
            Ast::Identifier(t) | Ast::Int(t) | Ast::Bool(t) => t.slice.clone(),
            Ast::Ref(inner) | Ast::Deref(inner) | Ast::Loop(inner) => inner.get_slice(),
            Ast::UnaryOp { op, operand } => {
                let start = op.slice.start;
                let end = operand.get_slice().start + operand.get_slice().len;
                Slice::new(start, end - start, op.slice.input)
            }
            Ast::BinaryOp { left, op, right } => {
                let start = left.get_slice().start;
                let end = right.get_slice().start + right.get_slice().len;
                Slice::new(start, end - start, op.slice.input)
            }
            Ast::VarDef {
                name,
                vartype: _,
                rhs,
            } => {
                let start = name.slice.start;
                let end = rhs.get_slice().start + rhs.get_slice().len;
                Slice::new(start, end - start, name.slice.input)
            }
            Ast::Reassign { lhs, rhs } => {
                let start = lhs.get_slice().start;
                let end = rhs.get_slice().start + rhs.get_slice().len;
                Slice::new(start, end - start, lhs.get_slice().input)
            }
            Ast::Statements(stmts) => {
                if stmts.is_empty() {
                    Slice::new(0, 0, "")
                } else {
                    let start = stmts.first().unwrap().get_slice().start;
                    let last = stmts.last().unwrap().get_slice();
                    let end = last.start + last.len;
                    Slice::new(start, end - start, last.input)
                }
            }
            Ast::IfElse {
                condition,
                ifbody,
                elsebody,
            } => {
                let start = condition.get_slice().start;
                let end = if let Some(else_ast) = elsebody {
                    let s = else_ast.get_slice();
                    s.start + s.len
                } else {
                    ifbody.get_slice().start + ifbody.get_slice().len
                };
                Slice::new(start, end - start, condition.get_slice().input)
            }
            Ast::Break(expr_opt) => {
                if let Some(expr) = expr_opt {
                    expr.get_slice()
                } else {
                    Slice::new(0, 0, "")
                }
            }
            Ast::Continue => Slice::new(0, 0, ""),
            Ast::Disp(ast) => ast.get_slice(),
        }
    }
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

    fn consume_line_end(&mut self) -> CompilerResult<'ip, ()> {
        expect_match!(self, TokenKind::LineEnd)?;
        Ok(())
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
                Some(Ok(tok)) if matches!(tok.kind, TokenKind::LineEnd) => {
                    self.consume_line_end()?
                }
                _ => stmts.push(Box::new(self.parse_statement()?)),
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
        let _ = self.next_token().ok_or(CompilerError::UnexpectedEof)??;
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
                let _eq = self.next_token().ok_or(CompilerError::UnexpectedEof)??;
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

        self.consume_line_end()?;
        Ok(Ast::Break(expr))
    }

    fn parse_statement(&mut self) -> CompilerResult<'ip, Ast<'ip>> {
        if let Some(Ok(tok)) = self.peek() {
            match &tok.kind {
                TokenKind::Keyword(Keyword::Var) => self.parse_vardef(),
                TokenKind::Keyword(Keyword::Disp) => {
                    expect_match!(self, TokenKind::Keyword(Keyword::Disp))?;
                    Ok(Ast::Disp(Box::new(self.parse_expression()?)))
                }
                TokenKind::Identifier(_) | TokenKind::Star => self.parse_reassign(),
                TokenKind::Keyword(Keyword::Break) => self.parse_break_stmt(),
                TokenKind::Keyword(Keyword::Continue) => {
                    expect_match!(self, TokenKind::Keyword(Keyword::Continue))?;
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
        if let Some(Ok(tok_ref)) = self.peek() {
            match tok_ref.kind {
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
                let _ = self.next_token().ok_or(CompilerError::UnexpectedEof)??;
                let operand = self.parse_ref()?;
                return Ok(Ast::Ref(Box::new(operand)));
            }
        }

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
            if let Some(Ok(peek)) = self.peek() {
                if matches!(peek.kind, TokenKind::LineEnd) {
                    self.consume_line_end()?;
                }
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
}
