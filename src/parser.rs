use std::iter::Peekable;

use crate::{
    error::{CompilerError, CompilerResult},
    lexer::{Lexer, Token, TokenKind},
};

#[derive(Debug)]
pub enum Ast<'ip> {
    // Identifier(Token<'ip>),
    Uint(Token<'ip>),
    UnaryOp {
        op: Token<'ip>,
        operand: Box<Ast<'ip>>,
    },
    BinaryOp {
        left: Box<Ast<'ip>>,
        op: Token<'ip>,
        right: Box<Ast<'ip>>,
    },
    Func {
        ident: Box<Ast<'ip>>,
        param: Box<Ast<'ip>>,
    },
}

fn parse_binary_op<'ip, F>(
    lexer: &mut Peekable<Lexer<'ip>>,
    operators: &[TokenKind], // allowed binary operators
    subparser: F,            // function to parse the lower precedence expression
) -> CompilerResult<'ip, Ast<'ip>>
where
    F: Fn(&mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>>,
{
    let mut node = subparser(lexer)?; // parse left-hand side

    while let Some(Ok(tok)) =
        lexer.next_if(|tok| matches!(tok, Ok(x) if operators.contains(&x.kind)))
    {
        node = Ast::BinaryOp {
            left: Box::new(node),
            op: tok,
            right: Box::new(subparser(lexer)?), // parse right-hand side
        };
    }

    // If its peek is an err, propagate it

    if let Some(Err(_)) = lexer.peek() {
        lexer.next().unwrap()?; // propagate error
    }

    Ok(node)
}

pub fn parse<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    expr(lexer)
}

fn expr<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    parse_binary_op(lexer, &[TokenKind::Plus, TokenKind::Minus], term)
}

fn term<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    parse_binary_op(lexer, &[TokenKind::Star, TokenKind::Slash], atom)
}

fn atom<'ip>(lexer: &mut Peekable<Lexer<'ip>>) -> CompilerResult<'ip, Ast<'ip>> {
    // if lexer returns none, we have an unexpected EOF error
    let token = lexer.next().ok_or(CompilerError::UnexpectedEof)??;
    let node = match token.kind {
        TokenKind::Uint(_) => Ast::Uint(token),
        // TokenKind::Identifier(_) => {
        //     let mut node = Ast::Identifier(token);

        //     if let Some(Ok(_)) =
        //         lexer.next_if(|x| matches!(x, Ok(x) if matches!(x.kind, TokenKind::Lparen)))
        //     {
        //         let param = expr(lexer)?;

        //         match lexer.next() {
        //             Some(Ok(tok)) if matches!(tok.kind, TokenKind::Rparen) => {}
        //             Some(Ok(got)) => {
        //                 return Err(CompilerError::UnexpectedToken { got, expected: ")" })
        //             }
        //             _ => return Err(CompilerError::UnexpectedEof),
        //         };

        //         node = Ast::Func {
        //             ident: Box::new(node),
        //             param: Box::new(param),
        //         };
        //     }

        //     node
        // }
        TokenKind::Minus => Ast::UnaryOp {
            op: token,
            operand: Box::new(atom(lexer)?),
        },
        TokenKind::Lparen => {
            let node = expr(lexer)?;

            match lexer.next() {
                Some(Ok(tok)) if matches!(tok.kind, TokenKind::Rparen) => node,
                Some(Ok(got)) => return Err(CompilerError::UnexpectedToken { got, expected: ")" }),
                _ => return Err(CompilerError::UnexpectedEof),
            }
        }
        _ => {
            return Err(CompilerError::UnexpectedToken {
                got: token,
                expected: "uint', '(', '-', 'ident",
            })
        }
    };

    Ok(node)
}
