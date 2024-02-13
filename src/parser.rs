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

        let mut lhs = match token {
            Token::Asterisk => {
                self.next_token();
                Expression::Everything
            }
            Token::Identifier(s) => {
                // todo: not all identifiers are attributes, some are functions etc. For now we assume they are all attributes
                self.next_token();

                match s.as_str() {
                    "true" => Expression::Literal(ast::LiteralKind::Boolean(true)),
                    "false" => Expression::Literal(ast::LiteralKind::Boolean(false)),
                    "null" => Expression::Literal(ast::LiteralKind::Null),
                    _ => Expression::Attr(s),
                }
            }
            Token::String(s) => {
                self.next_token();
                Expression::Literal(ast::LiteralKind::String(s))
            }

            Token::OpenBracket => self.parse_array_expr()?,

            // todo: split this into a separate function? Passing None for lhs isnt very intuitive
            // none = no lhs, so we are parsing an object
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

            token if is_prefix_operator(&token) => {
                let op = match parse_token_operator(&token) {
                    Some(op) => op,
                    None => Err(format!("unexpected token: {:?}", token))?,
                };

                self.next_token();

                let rbp = binding_power(&token, OperatorType::Prefix).1;
                let rhs = self.parse_expression(rbp)?;

                Expression::UnaryOp {
                    operator: op,
                    expr: Box::new(rhs),
                }
            }

            _ => Err(format!("unexpected token: {:?}", token))?,
        };

        loop {
            let next_token = self.peek_token().to_owned();
            if next_token == Token::EOF {
                self.next_token();
                break;
            }

            let (lbp, _) = binding_power(&next_token, OperatorType::Infix);
            if lbp < rbp {
                break;
            }

            lhs = match next_token {
                Token::OpenBracket => self.parse_bracket_expr(lhs)?,
                Token::OpenBrace => self.parse_brace_expr(Some(lhs))?,
                Token::Arrow => self.parse_arrow_deref(lhs)?,
                t if is_operator(&t) => self.parse_operator(lhs)?,
                // Nothing to do here, we've reached the end of the expression
                _ => break,
            };
        }

        Ok(lhs)
    }

    // Parses an array expression like [1, 2, 3], or [foo.bar[], bar]
    // To be used in the null denotation/lhs of the parser
    fn parse_array_expr(&mut self) -> Result<ast::Expression, String> {
        self.expect_token(Token::OpenBracket)?;

        let mut elements = Vec::new();

        let expr = self.parse_expression(0)?;
        elements.push(expr);

        while self.peek_token() == &Token::Comma {
            self.next_token();

            // Allow trailing comma
            if self.peek_token() == &Token::CloseBracket {
                break;
            }

            let expr = self.parse_expression(0)?;
            elements.push(expr);
        }

        self.expect_token(Token::CloseBracket)?;

        Ok(Expression::ArrayElements { elements })
    }

    // Parses a bracket suffix expression like foo[1], or foo[bar == "baz"]
    // To be used in the left denotation/rhs of the parser
    fn parse_bracket_expr(&mut self, lhs: Expression) -> Result<ast::Expression, String> {
        self.expect_token(Token::OpenBracket)?;

        let next_token = self.peek_token();
        if next_token == &Token::CloseBracket {
            self.expect_token(Token::CloseBracket)?;

            return Ok(Expression::ArrayPostfix {
                expr: Box::new(lhs),
            });
        }

        let expr = match self.parse_expression(0)? {
            Expression::Literal(LiteralKind::String(s)) => Expression::AttributeAccess {
                expr: Box::new(lhs),
                name: s,
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

            let attr = match self.parse_expression(0)? {
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

        // none = no lhs, so we are parsing an object
        match lhs {
            Some(lhs) => Ok(Expression::Projection {
                expr: Box::new(lhs),
                object: obj,
            }),
            None => Ok(Expression::Object(obj)),
        }
    }

    // Parses an expression with an operator, either prefix or infix
    fn parse_operator(&mut self, lhs: Expression) -> Result<ast::Expression, String> {
        let token = self.next_token();

        let op = match parse_token_operator(&token) {
            Some(op) => op,
            None => Err(format!("unexpected token: {:?}", token))?,
        };

        let (_, rbp) = binding_power(&token, OperatorType::Infix);
        let rhs = self.parse_expression(rbp)?;

        match op {
            Operator::Dot => {
                match (&lhs, &rhs) {
                    // When rhs is a Attr, we can convert this into an attribute access traversal
                    (_, Expression::Attr(rhs)) => Ok(Expression::AttributeAccess {
                        expr: Box::new(lhs),
                        name: rhs.to_string(),
                    }),

                    // TODO: is this valid, or should we error?
                    _ => Ok(Expression::BinaryOp {
                        lhs: Box::new(lhs),
                        operator: Operator::Dot,
                        rhs: Box::new(rhs),
                    }),
                }
            }
            _ => Ok(Expression::BinaryOp {
                lhs: Box::new(lhs),
                operator: op,
                rhs: Box::new(rhs),
            }),
        }
    }

    // Parses an deref traversal expression, e.g. foo->bar, or foo->
    fn parse_arrow_deref(&mut self, lhs: Expression) -> Result<ast::Expression, String> {
        self.expect_token(Token::Arrow)?;

        match self.peek_token().to_owned() {
            Token::Identifier(s) => {
                self.next_token();

                Ok(Expression::AttributeAccess {
                    expr: Box::new(Expression::Dereference {
                        expr: Box::new(lhs),
                    }),
                    name: s,
                })
            }
            _ => Ok(Expression::Dereference {
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

fn is_operator(token: &Token) -> bool {
    parse_token_operator(token).is_some()
}

fn is_prefix_operator(token: &Token) -> bool {
    match parse_token_operator(token) {
        Some(Operator::Not) => true,
        Some(Operator::Plus) => true,
        Some(Operator::Minus) => true,
        _ => false,
    }
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
    Postfix,
}

// Returns the left and right binding power for the given token and operator type
//
// Based on the GROQ precedence and associativity
// https://sanity-io.github.io/GROQ/GROQ-1.revision1/#sec-Precedence-and-associativity
// Level 11: Compound expressions.
// Level 10, prefix: +, !.
// Level 9, right-associative: **.
// Level 8, prefix: -.
// Level 7, left-associative: Multiplicatives (*, /, %).
// Level 6, left-associative: Additives (+, -).
// Level 5, non-associative: Ranges (.., ...).
// Level 4, non-associative: Comparisons (==, !=, >, >=,<, <=, in, match).
// Level 4, postfix: Ordering (asc, desc).
// Level 3, left-associative: &&.
// Level 2, left-associative: ||.
// Level 1, non-associative: =>.
fn binding_power(token: &Token, op: OperatorType) -> (u8, u8) {
    match op {
        OperatorType::Prefix => match token {
            Token::Not => (0, 100),                // Level 10, non-associative
            Token::Plus | Token::Minus => (0, 80), // Level 8, non-associative
            _ => (0, 0),
        },
        OperatorType::Infix => match token {
            Token::Colon => (10, 11), // For object attribute
            Token::Or => (20, 21),    // Level 2, left-associative
            Token::And => (30, 31),   // Level 3, left-associative
            Token::Eq | Token::NotEq | Token::Lt | Token::LtEq | Token::Gt | Token::GtEq => {
                (40, 40)
            } // Level 4, non-associative
            // Level 5 not implemented yet
            Token::Plus | Token::Minus => (60, 61), // Level 6, left-associative
            Token::Asterisk | Token::Slash | Token::Percent => (70, 71), // Level 7, left-associative
            Token::DoubleStar => (91, 90), // Level 9, right-associative
            // Level 11 not implemented yet
            _ => (0, 0),
        },
        OperatorType::Postfix => (0, 0),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! parser_test {
        ($($name:ident: $s:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let (query, expected) = $s;

                let lex: Lexer<'_> = Lexer::new(query);
                let mut parser = Parser::new(lex);
                let output = parser.parse().unwrap();

                assert_eq!(output, expected);
            }
        )*
        }
    }

    parser_test!(
        attr_access: ("foo.bar", Expression::AttributeAccess { expr: Box::new(Expression::Attr("foo".to_string())), name: "bar".to_string() }),

        attr_access_bracket: ("foo[\"bar\"]", Expression::AttributeAccess { expr: Box::new(Expression::Attr("foo".to_string())), name: "bar".to_string() }),

        attr_access_everything: ("*.bar", Expression::AttributeAccess { expr: Box::new(Expression::Everything), name: "bar".to_string() }),

        attr_access_everything_bracket: ("*['bar']", Expression::AttributeAccess { expr: Box::new(Expression::Everything), name: "bar".to_string() }),

        attr_access_object: (
            "{\"foo\": bar}.foo",
            Expression::AttributeAccess {
                expr: Box::new(Expression::Object(ast::Object {
                    entries: vec![
                        ast::ObjectAttribute::AliasedExpression{
                            alias: "foo".to_string(),
                            expr: Box::new(Expression::Attr("bar".to_string()))
                        },
                    ]})
                ),
                name: "foo".to_string()
            }
        ),

        array_elements: ("[1, 2, 3]", Expression::ArrayElements { elements: vec![Expression::Literal(LiteralKind::Int64(1)), Expression::Literal(LiteralKind::Int64(2)), Expression::Literal(LiteralKind::Int64(3))] }),

        array_postfix: ("foo[]", Expression::ArrayPostfix { expr: Box::new(Expression::Attr("foo".to_string())) }),

        array_postfix_with_filter: (
            "foo[bar == 'baz']",
            Expression::FilterTraversal {
                expr: Box::new(Expression::Attr("foo".to_string())),
                constraint: Box::new(Expression::BinaryOp { lhs: Box::new(Expression::Attr("bar".to_string())), operator: Operator::Eq, rhs: Box::new(Expression::Literal(LiteralKind::String("baz".to_string())))
            })
        }),

        array_chained_ints: (
            "[1, 2, [3, 4, 5]][3][0]",
            Expression::ElementAccess {
                expr: Box::new(Expression::ElementAccess {
                    expr: Box::new(Expression::ArrayElements {
                        elements: vec![
                            Expression::Literal(LiteralKind::Int64(1)),
                            Expression::Literal(LiteralKind::Int64(2)),
                            Expression::ArrayElements {
                                elements: vec![
                                    Expression::Literal(LiteralKind::Int64(3)),
                                    Expression::Literal(LiteralKind::Int64(4)),
                                    Expression::Literal(LiteralKind::Int64(5)),
                                ]
                            }
                        ]
                    }),
                    index: Box::new(Expression::Literal(LiteralKind::Int64(3))),
                }),
                index: Box::new(Expression::Literal(LiteralKind::Int64(0))),
            }
        ),

        array_bool: (
            "[true, false, null][0]",
            Expression::ElementAccess {
                expr: Box::new(Expression::ArrayElements {
                    elements: vec![
                        Expression::Literal(LiteralKind::Boolean(true)),
                        Expression::Literal(LiteralKind::Boolean(false)),
                        Expression::Literal(LiteralKind::Null),
                    ]
                }),
                index: Box::new(Expression::Literal(LiteralKind::Int64(0))),
            }
        ),

        object: (
            "{\"foo\": bar, \"baz\": 2}",
            Expression::Object(ast::Object {
                entries: vec![
                    ast::ObjectAttribute::AliasedExpression {
                        alias: "foo".to_string(),
                        expr: Box::new(Expression::Attr("bar".to_string()))
                    },
                    ast::ObjectAttribute::AliasedExpression {
                        alias: "baz".to_string(),
                        expr: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                    },
                ]
            })
        ),

        object_nested: (
            "{\"foo\": {\"bar\": 2}}",
            Expression::Object(ast::Object {
                entries: vec![
                    ast::ObjectAttribute::AliasedExpression {
                        alias: "foo".to_string(),
                        expr: Box::new(Expression::Object(ast::Object {
                            entries: vec![
                                ast::ObjectAttribute::AliasedExpression {
                                    alias: "bar".to_string(),
                                    expr: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                                }
                            ]
                        }))
                    }
                ]
            })
        ),

        dereference: (
            "foo->bar",
            Expression::AttributeAccess {
                expr: Box::new(Expression::Dereference { expr: Box::new(Expression::Attr("foo".to_string())) }),
                name: "bar".to_string()
            },
        ),

        dereference_nested_array: (
            "bar[]->meta->title.en",
            Expression::AttributeAccess {
                expr: Box::new(Expression::AttributeAccess {
                    expr: Box::new(Expression::Dereference {
                        expr: Box::new(Expression::AttributeAccess {
                            expr: Box::new(Expression::Dereference {
                                expr: Box::new(Expression::ArrayPostfix { expr: Box::new(Expression::Attr("bar".to_string())) })
                            }),
                            name: "meta".to_string()
                        })
                    }),
                    name: "title".to_string()
                }),
                name: "en".to_string()
            }
        ),

        dereference_projection: (
            "foo->{bar, baz}",
            Expression::Projection {
                expr: Box::new(Expression::Dereference { expr: Box::new(Expression::Attr("foo".to_string())) }),
                object: ast::Object {
                    entries: vec![
                        ast::ObjectAttribute::Expression(Box::new(Expression::Attr("bar".to_string()))),
                        ast::ObjectAttribute::Expression(Box::new(Expression::Attr("baz".to_string()))),
                    ]
                }
            }
        ),

        dereference_projection_attr_access: (
            "foo->{bar, baz}.bar",
            Expression::AttributeAccess {
                expr: Box::new(Expression::Projection {
                    expr: Box::new(Expression::Dereference { expr: Box::new(Expression::Attr("foo".to_string())) }),
                    object: ast::Object {
                        entries: vec![
                            ast::ObjectAttribute::Expression(Box::new(Expression::Attr("bar".to_string()))),
                            ast::ObjectAttribute::Expression(Box::new(Expression::Attr("baz".to_string()))),
                        ]
                    }
                }),
                name: "bar".to_string()
            }
        ),

        // TODO: Need implementation for this
        ranged_slice_exl: (
            "foo[1..3]",
            Expression::SliceTraversal {
                range: ast::Range {
                    start: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                    end: Box::new(Expression::Literal(LiteralKind::Int64(3))),
                    inclusive: false,
                }
            }
        ),
    );

    // Tests for precedence and associativity
    // https://sanity-io.github.io/GROQ/GROQ-1.revision1/#sec-Precedence-and-associativity
    // Level 11: Compound expressions.
    // Level 10, prefix: +, !.
    // Level 9, right-associative: **.
    // Level 8, prefix: -.
    // Level 7, left-associative: Multiplicatives (*, /, %).
    // Level 6, left-associative: Additives (+, -).
    // Level 5, non-associative: Ranges (.., ...).
    // Level 4, non-associative: Comparisons (==, !=, >, >=,<, <=, in, match).
    // Level 4, postfix: Ordering (asc, desc).
    // Level 3, left-associative: &&.
    // Level 2, left-associative: ||.
    // Level 1, non-associative: =>.
    parser_test!(
        // => is not implemented yet
        // level_1:

        level_2: (
            "true || false || true",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::Literal(LiteralKind::Boolean(true))),
                    operator: Operator::Or,
                    rhs: Box::new(Expression::Literal(LiteralKind::Boolean(false)))
                }),
                operator: Operator::Or,
                rhs: Box::new(Expression::Literal(LiteralKind::Boolean(true)))
            }
        ),

        level_3: (
            "true && false && true",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::Literal(LiteralKind::Boolean(true))),
                    operator: Operator::And,
                    rhs: Box::new(Expression::Literal(LiteralKind::Boolean(false)))
                }),
                operator: Operator::And,
                rhs: Box::new(Expression::Literal(LiteralKind::Boolean(true)))
            }
        ),

        level_3_2: (
            "true || false && false || true",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::Literal(LiteralKind::Boolean(true))),
                    operator: Operator::Or,
                    rhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Boolean(false))),
                        operator: Operator::And,
                        rhs: Box::new(Expression::Literal(LiteralKind::Boolean(false)))
                    })
                }),
                operator: Operator::Or,
                rhs: Box::new(Expression::Literal(LiteralKind::Boolean(true)))
            }
        ),

        level_3_2a: (
            "true && false || false && true",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::Literal(LiteralKind::Boolean(true))),
                    operator: Operator::And,
                    rhs: Box::new(Expression::Literal(LiteralKind::Boolean(false)))
                }),
                operator: Operator::Or,
                rhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::Literal(LiteralKind::Boolean(false))),
                    operator: Operator::And,
                    rhs: Box::new(Expression::Literal(LiteralKind::Boolean(true)))
                })
            }
        ),

        level_4_ands: (
            "1 == 2 && 3 != 4 && 5 > 6 && 7 >= 8 && 9 < 10 && 11 <= 12",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::BinaryOp {
                            lhs: Box::new(Expression::BinaryOp {
                                lhs: Box::new(Expression::BinaryOp {
                                    lhs: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                                    operator: Operator::Eq,
                                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                                }),
                                operator: Operator::And,
                                rhs: Box::new(Expression::BinaryOp {
                                    lhs: Box::new(Expression::Literal(LiteralKind::Int64(3))),
                                    operator: Operator::NotEq,
                                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(4)))
                                })
                            }),
                            operator: Operator::And,
                            rhs: Box::new(Expression::BinaryOp {
                                lhs: Box::new(Expression::Literal(LiteralKind::Int64(5))),
                                operator: Operator::Gt,
                                rhs: Box::new(Expression::Literal(LiteralKind::Int64(6)))
                            })
                        }),
                        operator: Operator::And,
                        rhs: Box::new(Expression::BinaryOp {
                            lhs: Box::new(Expression::Literal(LiteralKind::Int64(7))),
                            operator: Operator::GtEq,
                            rhs: Box::new(Expression::Literal(LiteralKind::Int64(8)))
                        })
                    }),
                    operator: Operator::And,
                    rhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(9))),
                        operator: Operator::Lt,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(10)))
                    })
                }),
                operator: Operator::And,
                rhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::Literal(LiteralKind::Int64(11))),
                    operator: Operator::LtEq,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(12)))
                }),
            }
        ),

        level_4_ors: (
            "1 == 2 || 3 != 4 || 5 > 6 || 7 >= 8 || 9 < 10 || 11 <= 12",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::BinaryOp {
                            lhs: Box::new(Expression::BinaryOp {
                                lhs: Box::new(Expression::BinaryOp {
                                    lhs: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                                    operator: Operator::Eq,
                                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                                }),
                                operator: Operator::Or,
                                rhs: Box::new(Expression::BinaryOp {
                                    lhs: Box::new(Expression::Literal(LiteralKind::Int64(3))),
                                    operator: Operator::NotEq,
                                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(4)))
                                })
                            }),
                            operator: Operator::Or,
                            rhs: Box::new(Expression::BinaryOp {
                                lhs: Box::new(Expression::Literal(LiteralKind::Int64(5))),
                                operator: Operator::Gt,
                                rhs: Box::new(Expression::Literal(LiteralKind::Int64(6)))
                            })
                        }),
                        operator: Operator::Or,
                        rhs: Box::new(Expression::BinaryOp {
                            lhs: Box::new(Expression::Literal(LiteralKind::Int64(7))),
                            operator: Operator::GtEq,
                            rhs: Box::new(Expression::Literal(LiteralKind::Int64(8)))
                        })
                    }),
                    operator: Operator::Or,
                    rhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(9))),
                        operator: Operator::Lt,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(10)))
                    })
                }),
                operator: Operator::Or,
                rhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::Literal(LiteralKind::Int64(11))),
                    operator: Operator::LtEq,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(12)))
                }),
            }
        ),

        level_4_ands_ors: (
            "1 == 2 && 3 != 4 || 5 > 6 && 7 >= 8 || 9 < 10 && 11 <= 12",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::BinaryOp {
                            lhs: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                            operator: Operator::Eq,
                            rhs: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                        }),
                        operator: Operator::And,
                        rhs: Box::new(Expression::BinaryOp {
                            lhs: Box::new(Expression::Literal(LiteralKind::Int64(3))),
                            operator: Operator::NotEq,
                            rhs: Box::new(Expression::Literal(LiteralKind::Int64(4)))
                        })
                    }),
                    operator: Operator::Or,
                    rhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::BinaryOp {
                            lhs: Box::new(Expression::Literal(LiteralKind::Int64(5))),
                            operator: Operator::Gt,
                            rhs: Box::new(Expression::Literal(LiteralKind::Int64(6)))
                        }),
                        operator: Operator::And,
                        rhs: Box::new(Expression::BinaryOp {
                            lhs: Box::new(Expression::Literal(LiteralKind::Int64(7))),
                            operator: Operator::GtEq,
                            rhs: Box::new(Expression::Literal(LiteralKind::Int64(8)))
                        })
                    })
                }),
                operator: Operator::Or,
                rhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(9))),
                        operator: Operator::Lt,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(10)))
                    }),
                    operator: Operator::And,
                    rhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(11))),
                        operator: Operator::LtEq,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(12)))
                    })
                }),
            }
        ),

        // Rang(.., ...) not implemented yet
        // level_5:

        level_6: (
            "1 + 2 - 3 + 4",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                        operator: Operator::Plus,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                    }),
                    operator: Operator::Minus,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(3)))
                }),
                operator: Operator::Plus,
                rhs: Box::new(Expression::Literal(LiteralKind::Int64(4)))
            }
        ),

        level_6_2: (
            "1 + 2 || 3 - 4 && 5 + 6",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                    operator: Operator::Plus,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                }),
                operator: Operator::Or,
                rhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(3))),
                        operator: Operator::Minus,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(4)))
                    }),
                    operator: Operator::And,
                    rhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(5))),
                        operator: Operator::Plus,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(6)))
                    })
                })
            }
        ),

        level_7: (
            "1 * 2 / 3 % 4",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                        operator: Operator::Star,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                    }),
                    operator: Operator::Slash,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(3)))
                }),
                operator: Operator::Percent,
                rhs: Box::new(Expression::Literal(LiteralKind::Int64(4)))
            }
        ),

        level_7_6: (
            "1 * 2 / 3 + 4 * 5 % 6",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                        operator: Operator::Star,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                    }),
                    operator: Operator::Slash,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(3)))
                }),
                operator: Operator::Plus,
                rhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(4))),
                        operator: Operator::Star,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(5)))
                    }),
                    operator: Operator::Percent,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(6)))
                })
            }
        ),

        level_7_2_3: (
            "1 * 2 || 3 / 4 && 5 * 6",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                    operator: Operator::Star,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                }),
                operator: Operator::Or,
                rhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(3))),
                        operator: Operator::Slash,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(4)))
                    }),
                    operator: Operator::And,
                    rhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(5))),
                        operator: Operator::Star,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(6)))
                    })
                })
            }
        ),

        level_8: (
            "+1 - 2",
            Expression::BinaryOp {
                lhs: Box::new(Expression::UnaryOp {
                    operator: Operator::Plus,
                    expr: Box::new(Expression::Literal(LiteralKind::Int64(1)))
                }),
                operator: Operator::Minus,
                rhs: Box::new(Expression::Literal(LiteralKind::Int64(2)))
            }
        ),

        level_8_7: (
            "+1 * 2 - -3 / 4",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::UnaryOp {
                        operator: Operator::Plus,
                        expr: Box::new(Expression::Literal(LiteralKind::Int64(1)))
                    }),
                    operator: Operator::Star,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                }),
                operator: Operator::Minus,
                rhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::UnaryOp {
                        operator: Operator::Minus,
                        expr: Box::new(Expression::Literal(LiteralKind::Int64(3)))
                    }),
                    operator: Operator::Slash,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(4)))
                })
            }
        ),

        level_8_2_3: (
            "+1 || 2 - -3 && 4",
            Expression::BinaryOp {
                lhs: Box::new(Expression::UnaryOp {
                    operator: Operator::Plus,
                    expr: Box::new(Expression::Literal(LiteralKind::Int64(1)))
                }),
                operator: Operator::Or,
                rhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(2))),
                        operator: Operator::Minus,
                        rhs: Box::new(Expression::UnaryOp {
                            operator: Operator::Minus,
                            expr: Box::new(Expression::Literal(LiteralKind::Int64(3)))
                        }),
                    }),
                    operator: Operator::And,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(4)))
                })
            }
        ),

        level_9: (
            "1 ** 2 ** 3",
            Expression::BinaryOp {
                lhs: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                operator: Operator::DoubleStar,
                rhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::Literal(LiteralKind::Int64(2))),
                    operator: Operator::DoubleStar,
                    rhs: Box::new(Expression::Literal(LiteralKind::Int64(3)))
                })
            }
        ),

        level_9_8: (
            "1 ** +2 ** -3",
            Expression::BinaryOp {
                lhs: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                operator: Operator::DoubleStar,
                rhs: Box::new(Expression::UnaryOp {
                    operator: Operator::Plus,
                    expr: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(2))),
                        operator: Operator::DoubleStar,
                        rhs: Box::new(Expression::UnaryOp {
                            operator: Operator::Minus,
                            expr: Box::new(Expression::Literal(LiteralKind::Int64(3)))
                        })
                    })
                })
            }
        ),

        level_9_8_2: (
            "1 ** +2 || -3 ** 4",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::Literal(LiteralKind::Int64(1))),
                    operator: Operator::DoubleStar,
                    rhs: Box::new(Expression::UnaryOp {
                        operator: Operator::Plus,
                        expr: Box::new(Expression::Literal(LiteralKind::Int64(2)))
                    }),
                }),
                operator: Operator::Or,
                rhs: Box::new(Expression::UnaryOp {
                    operator: Operator::Minus,
                    expr: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::Literal(LiteralKind::Int64(3))),
                        operator: Operator::DoubleStar,
                        rhs: Box::new(Expression::Literal(LiteralKind::Int64(4)))
                    })
                })
            }
        ),

        level_10: (
            "!true",
            Expression::UnaryOp {
                operator: Operator::Not,
                expr: Box::new(Expression::Literal(LiteralKind::Boolean(true)))
            }
        ),

        level_10_2_3: (
            "!true || !false && !true || true",
            Expression::BinaryOp {
                lhs: Box::new(Expression::BinaryOp {
                    lhs: Box::new(Expression::UnaryOp {
                        operator: Operator::Not,
                        expr: Box::new(Expression::Literal(LiteralKind::Boolean(true)))
                    }),
                    operator: Operator::Or,
                    rhs: Box::new(Expression::BinaryOp {
                        lhs: Box::new(Expression::UnaryOp {
                            operator: Operator::Not,
                            expr: Box::new(Expression::Literal(LiteralKind::Boolean(false)))
                        }),
                        operator: Operator::And,
                        rhs: Box::new(Expression::UnaryOp {
                            operator: Operator::Not,
                            expr: Box::new(Expression::Literal(LiteralKind::Boolean(true)))
                        }),
                    })
                }),
                operator: Operator::Or,
                rhs: Box::new(Expression::Literal(LiteralKind::Boolean(true)))
            }
        ),
    );

    #[test]
    fn test_print_output() {
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
