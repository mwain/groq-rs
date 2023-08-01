use std::collections::VecDeque;

use crate::ast::{self, Expression, LiteralKind, Operator};
use crate::lexer::{Lexer, Token};

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    buffer: VecDeque<Token>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Parser {
            lexer,
            buffer: VecDeque::new(),
        }
    }

    pub fn parse(&mut self) -> Result<ast::Expression, String> {
        self.parse_expression(0)
    }

    fn parse_expression(&mut self, rbp: u8) -> Result<ast::Expression, String> {
        // Top Down Operator Precedence / Pratt Parser

        let token = self.peek_token().to_owned();

        // Parse the left hand side, the null denotation
        let mut lhs = match token {
            Token::Asterisk => {
                self.next_token();
                Expression::Everything
            }
            Token::Identifier(s) => {
                // todo: not all identifiers are attributes, some are functions etc. For now we assume they are all attributes
                self.next_token();
                Expression::AttributeAccess(s)
            }
            Token::String(s) => {
                self.next_token();
                Expression::Literal(ast::LiteralKind::String(s))
            }

            Token::OpenBracket => self.parse_array_expr()?,

            // todo: split this into a separate function? Passing None for lhs isnt very intuitive
            Token::OpenBrace => self.parse_brace_expr(None)?,

            Token::Number(n) => {
                self.next_token();
                let int = match n.parse::<i64>() {
                    Ok(i) => i,
                    Err(e) => Err(format!("failed to parse number into integer: {e}"))?,
                };
                Expression::Literal(ast::LiteralKind::Int64(int))
            }
            Token::Float(n) => {
                self.next_token();
                let float = match n.parse::<f64>() {
                    Ok(f) => f,
                    Err(e) => Err(format!("failed to parse number into float: {e}"))?,
                };
                Expression::Literal(ast::LiteralKind::Float64(float))
            }
            _ => Err(format!("unexpected token: {:?}", token))?,
        };

        loop {
            let next_token = self.peek_token().to_owned();
            if next_token == Token::EOF {
                self.next_token();
                break;
            }

            let lbp = binding_power(&next_token);
            if lbp < rbp {
                break;
            }

            // Parse the right hand side, the left denotation
            lhs = match next_token {
                Token::OpenBracket => self.parse_bracket_expr(lhs)?,
                Token::OpenBrace => self.parse_brace_expr(Some(lhs))?,
                Token::Arrow => self.parse_arrow_deref(lhs)?,
                t if is_operator(&t) => self.parse_operator(lhs)?,
                _ => Err(format!("unexpected token: {:?}", next_token))?,
            };
        }

        Ok(lhs)
    }

    // Parses an array expression like [1, 2, 3], or [foo.bar[], bar]
    // To be used in the null denotation/lhs of the parser
    fn parse_array_expr(&mut self) -> Result<ast::Expression, String> {
        self.expect_token(Token::OpenBracket)?;

        let mut elements = Vec::new();

        let expr = self.parse_expression(1)?;
        elements.push(expr);

        while self.peek_token() == &Token::Comma {
            self.next_token();

            // Allow trailing comma
            if self.peek_token() == &Token::CloseBracket {
                break;
            }

            let expr = self.parse_expression(1)?;
            elements.push(expr);
        }

        self.expect_token(Token::CloseBracket)?;

        Ok(Expression::Array { elements })
    }

    // Parses a bracket suffix expression like foo[1], or foo[bar == "baz"]
    // To be used in the left denotation/rhs of the parser
    fn parse_bracket_expr(&mut self, lhs: Expression) -> Result<ast::Expression, String> {
        self.expect_token(Token::OpenBracket)?;

        let next_token = self.peek_token();
        if next_token == &Token::CloseBracket {
            self.expect_token(Token::CloseBracket)?;

            return Ok(Expression::ArrayTraversal {
                expr: Box::new(lhs),
            });
        }

        let expr = match self.parse_expression(1)? {
            Expression::Literal(LiteralKind::String(s)) => Expression::BinaryOp {
                lhs: Box::new(lhs),
                operator: ast::Operator::Dot,
                rhs: Box::new(Expression::AttributeAccess(s)),
            },

            // TODO: need to further disambiguating square brackets
            // see https://sanity-io.github.io/GROQ/draft/#sec-Disambiguating-square-bracket-traversal
            Expression::Literal(LiteralKind::Int64(i)) => Expression::ElementAccess {
                expr: Box::new(lhs),
                index: Box::new(Expression::Literal(LiteralKind::Int64(i))),
            },

            constraint => Expression::FilterTraversal {
                expr: Box::new(lhs),
                constraint: Box::new(constraint),
            },
        };

        self.expect_token(Token::CloseBracket)?;

        Ok(expr)
    }

    // Parses an expression inside braces, either an object or a projection
    fn parse_brace_expr(&mut self, lhs: Option<Expression>) -> Result<ast::Expression, String> {
        self.expect_token(Token::OpenBrace)?;

        let mut entries = Vec::new();
        loop {
            let token = self.peek_token();
            if token == &Token::CloseBrace {
                break;
            }

            let attr = match self.parse_expression(1)? {
                Expression::BinaryOp {
                    lhs,
                    operator: Operator::Colon,
                    rhs,
                } => match *lhs {
                    Expression::Literal(LiteralKind::String(s)) => {
                        ast::ObjectAttribute::AliasedExpression {
                            alias: s,
                            expr: rhs,
                        }
                    }
                    _ => Err(format!("expected string literal, got {:?}", lhs))?,
                },
                expr => ast::ObjectAttribute::Expression(Box::new(expr)),
            };

            entries.push(attr);

            if self.peek_token() == &Token::Comma {
                self.next_token();
            }
        }

        self.expect_token(Token::CloseBrace)?;

        let obj: ast::Object = ast::Object { entries };

        match lhs {
            Some(lhs) => Ok(Expression::ProjectionTraversal {
                expr: Box::new(lhs),
                object: obj,
            }),
            None => Ok(Expression::Object(obj)),
        }
    }

    // Parses an expression with an operator, either prefix or infix
    // A left denotation/rhs of the parser
    fn parse_operator(&mut self, lhs: Expression) -> Result<ast::Expression, String> {
        let token = self.next_token();

        let op = match token_into_operator(&token) {
            Some(op) => op,
            None => Err(format!("unexpected token: {:?}", token))?,
        };

        match op {
            (OperatorType::Prefix, op, rbp) => {
                let rhs = self.parse_expression(rbp)?;
                Ok(Expression::UnaryOp {
                    operator: op,
                    expr: Box::new(rhs),
                })
            }

            (OperatorType::Infix, op, rbp) => {
                let rhs = self.parse_expression(rbp)?;
                Ok(Expression::BinaryOp {
                    lhs: Box::new(lhs),
                    operator: op,
                    rhs: Box::new(rhs),
                })
            }
        }
    }

    // Parses an deref traversal expression, e.g. foo->bar, or foo->
    fn parse_arrow_deref(&mut self, lhs: Expression) -> Result<ast::Expression, String> {
        self.expect_token(Token::Arrow)?;

        match self.peek_token().to_owned() {
            Token::Identifier(s) => {
                self.next_token();

                Ok(Expression::BinaryOp {
                    lhs: Box::new(Expression::DereferenceTraversal {
                        expr: Box::new(lhs),
                    }),
                    operator: Operator::Dot,
                    rhs: Box::new(Expression::AttributeAccess(s)),
                })
            }
            _ => Ok(Expression::DereferenceTraversal {
                expr: Box::new(lhs),
            }),
        }
    }

    fn peek_token(&mut self) -> &Token {
        if self.buffer.is_empty() {
            let token = self.lexer.next_token();
            self.buffer.push_back(token);
        }

        match self.buffer.front() {
            Some(token) => token,
            None => &Token::EOF,
        }
    }

    fn next_token(&mut self) -> Token {
        if self.buffer.is_empty() {
            self.lexer.next_token()
        } else {
            match self.buffer.pop_front() {
                Some(token) => token,
                None => Token::EOF,
            }
        }
    }

    // Consumes the next token if it matches the expected token, otherwise returns an error
    fn expect_token(&mut self, expected: Token) -> Result<(), String> {
        if self.peek_token() == &expected {
            self.next_token();
            Ok(())
        } else {
            Err(format!(
                "unexpected token: {:?}, expected {:?}",
                self.peek_token(),
                expected
            ))
        }
    }
}

fn binding_power(token: &Token) -> u8 {
    match token {
        Token::OpenBracket | Token::OpenBrace => 100,
        Token::Dot => 90,
        Token::Arrow => 80,
        Token::Eq | Token::NotEq | Token::Lt | Token::LtEq | Token::Gt | Token::GtEq => 40,
        Token::And => 30,
        Token::Or => 30,
        Token::Colon => 10,
        _ => 0,
    }
}

fn is_operator(token: &Token) -> bool {
    parse_token_operator(token).is_some()
}

fn parse_token_operator(token: &Token) -> Option<ast::Operator> {
    match token {
        Token::And => Some(ast::Operator::And),
        Token::Or => Some(ast::Operator::Or),
        Token::Not => Some(ast::Operator::Not),
        Token::Eq => Some(ast::Operator::Eq),
        Token::NotEq => Some(ast::Operator::NotEq),
        Token::Lt => Some(ast::Operator::Lt),
        Token::LtEq => Some(ast::Operator::LtEq),
        Token::Gt => Some(ast::Operator::Gt),
        Token::GtEq => Some(ast::Operator::GtEq),
        Token::Plus => Some(ast::Operator::Plus),
        Token::Minus => Some(ast::Operator::Minus),
        Token::Asterisk => Some(ast::Operator::Star),
        Token::Slash => Some(ast::Operator::Slash),
        Token::Percent => Some(ast::Operator::Percent),
        Token::DoubleStar => Some(ast::Operator::DoubleStar),
        Token::Dot => Some(ast::Operator::Dot),
        Token::Dots(3) => Some(ast::Operator::DotDotDot),
        Token::Colon => Some(ast::Operator::Colon),
        _ => None,
    }
}

enum OperatorType {
    Prefix,
    Infix,
}

fn token_into_operator(token: &Token) -> Option<(OperatorType, ast::Operator, u8)> {
    match parse_token_operator(token) {
        // Prefix operators
        Some(ast::Operator::Not) => Some((
            OperatorType::Prefix,
            ast::Operator::Not,
            binding_power(token),
        )),

        // Infix operators, the rest...
        Some(op) => Some((OperatorType::Infix, op, binding_power(token))),

        None => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parser() {
        let lex: Lexer<'_> = Lexer::new(
            r#"
            {
                "foo": "bar",
                "everything": *[_type == 'foo'],
                "metadata": bar[]->meta->title.en
            }
        "#,
        );
        let mut parser = Parser::new(lex);
        let output = parser.parse();
        println!("{:#?}", output);
    }

    #[test]
    fn test_peeking_consume() {
        let lex: Lexer<'_> = Lexer::new(" *[_type == 'foo'] ");
        let mut parser = Parser::new(lex);

        assert_eq!(parser.peek_token(), &Token::Asterisk);
        assert_eq!(parser.next_token(), Token::Asterisk);

        assert_eq!(parser.peek_token(), &Token::OpenBracket);
        assert_eq!(parser.peek_token(), &Token::OpenBracket);
        assert_eq!(parser.next_token(), Token::OpenBracket);
    }
}
