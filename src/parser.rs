use core::ops::ControlFlow;
use std::collections::VecDeque;

use crate::ast::{self, *};
use crate::lexer::{Lexer, Token};
use crate::visit;

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

    pub fn parse(&mut self) -> Result<Box<Expression>, String> {
        self.parse_expression(0)
    }

    fn parse_expression(&mut self, rbp: u8) -> Result<Box<Expression>, String> {
        // Top Down Operator Precedence / Pratt Parser

        let token = self.peek_token().to_owned();
        println!("-- parse_expression: {:?}, rbp: {} ---", token, rbp);

        let mut lhs = match token {
            Token::Asterisk => {
                self.next_token();
                make_expr(ExpressionKind::Everything)
            }
            Token::Identifier(s) => {
                // todo: not all identifiers are attributes, some are functions etc. For now we assume they are all attributes
                self.next_token();
                make_expr(match s.as_str() {
                    "true" => ExpressionKind::Literal(LiteralKind::Boolean(true)),
                    "false" => ExpressionKind::Literal(LiteralKind::Boolean(false)),
                    "null" => ExpressionKind::Literal(LiteralKind::Null),
                    _ => ExpressionKind::Attr(s),
                })
            }
            Token::String(s) => {
                self.next_token();
                make_expr(ExpressionKind::Literal(LiteralKind::String(s)))
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
                make_expr(ExpressionKind::Literal(ast::LiteralKind::Int64(int)))
            }
            Token::Float(n) => {
                self.next_token();
                let float = match n.parse::<f64>() {
                    Ok(f) => f,
                    Err(e) => Err(format!("failed to parse number into float: {e}"))?,
                };
                make_expr(ExpressionKind::Literal(LiteralKind::Float64(float)))
            }

            token if is_prefix_operator(&token) => {
                let op = match parse_token_operator(&token) {
                    Some(op) => op,
                    None => Err(format!("unexpected token: {:?}", token))?,
                };

                self.next_token();

                let rbp = binding_power(&token, OperatorType::Prefix).1;
                let rhs = self.parse_expression(rbp)?;

                make_expr(ExpressionKind::UnaryOp(UnaryOp {
                    operator: op,
                    expr: rhs,
                }))
            }

            _ => Err(format!("unexpected token: {:?}", token))?,
        };

        let mut counter = 0;
        loop {
            let next_token = self.peek_token().to_owned();
            if next_token == Token::EOF {
                self.next_token();
                break;
            }

            println!("---- rhs {counter}",);

            if is_postfix_operator(&next_token) {
                let (lbp, _) = binding_power(&next_token, OperatorType::Postfix);
                println!(
                    "postfix_next_token: {:?}, lbp: {}, rbp: {}",
                    next_token, lbp, rbp
                );

                if lbp < rbp {
                    print!("-- break rhs postfix ---");
                    break;
                }

                lhs = match next_token {
                    Token::EmptyBrackets => {
                        self.expect_token(Token::EmptyBrackets)?;
                        make_expr(ExpressionKind::ArrayPostfix(ArrayPostfix { expr: lhs }))
                    }
                    _ => Err(format!("unexpected token: {:?}", next_token))?,
                };
                continue;
            }

            let (lbp, _) = binding_power(&next_token, OperatorType::Infix);
            println!("next_token: {:?}, lbp: {}, rbp: {}", next_token, lbp, rbp);

            lhs = match next_token {
                Token::OpenBracket => self.parse_bracket_expr(lhs)?,
                Token::OpenBrace => self.parse_brace_expr(Some(lhs))?,
                Token::Arrow => self.parse_arrow_deref(lhs)?,
                t if is_operator(&t) => {
                    if lbp < rbp {
                        print!("-- break rhs ---");
                        break;
                    }

                    self.parse_operator(lhs)?
                }
                // Nothing to do here, we've reached the end of the expression
                _ => {
                    print!("-- break rhs nothing ---");
                    break;
                }
            };

            counter += 1;
            println!("---- done rhs {counter} {:?}", lhs);
        }

        println!("-- end parse_expression ---");

        Ok(lhs)
    }

    // Parses an array expression like [1, 2, 3], or [foo.bar[], bar]
    fn parse_array_expr(&mut self) -> Result<Box<Expression>, String> {
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

        Ok(make_expr(ExpressionKind::ArrayElements(ArrayElements {
            elements: elements.into_iter().map(|expr| *expr).collect(),
        })))
    }

    // Parses a bracket suffix expression like foo[1], foo[bar == "baz"] and foo[1..2]
    fn parse_bracket_expr(&mut self, lhs: Box<Expression>) -> Result<Box<Expression>, String> {
        self.expect_token(Token::OpenBracket)?;

        println!("-- parse_bracket_expr");

        // "Disambiguating square bracket traversal" - https://sanity-io.github.io/GROQ/draft/#sec-Disambiguating-square-backet-traversal

        let parsed_expr = self.parse_expression(0)?;
        let kind = match parsed_expr.kind {
            ExpressionKind::Literal(LiteralKind::String(s)) => {
                ExpressionKind::AttributeAccess(AttributeAccess { expr: lhs, name: s })
            }

            ExpressionKind::Literal(LiteralKind::Int64(_)) => {
                ExpressionKind::ElementAccess(ElementAccess {
                    expr: lhs,
                    index: parsed_expr,
                })
            }

            ExpressionKind::Range(range) => {
                let lhs_constant = is_constant_evaluate(&range.start, &LiteralKind::Int64(0));
                let rhs_constant = is_constant_evaluate(&range.end, &LiteralKind::Int64(0));

                if lhs_constant && rhs_constant {
                    ExpressionKind::SliceTraversal(SliceTraversal {
                        range: ast::Range {
                            start: range.start,
                            end: range.end,
                            inclusive: range.inclusive,
                        },
                    })
                } else {
                    ExpressionKind::FilterTraversal(FilterTraversal {
                        expr: lhs,
                        constraint: make_expr(ExpressionKind::Range(range)),
                    })
                }
            }

            _ => {
                if is_constant_evaluate(&parsed_expr, &LiteralKind::Int64(0)) {
                    ExpressionKind::ElementAccess(ElementAccess{
                        expr: lhs,
                        index: parsed_expr,
                    })
                } else {
                    ExpressionKind::FilterTraversal(FilterTraversal {
                        expr: lhs,
                        constraint: parsed_expr,
                    })
                }
            }
        };

        self.expect_token(Token::CloseBracket)?;

        println!("-- end parse_bracket_expr");
        Ok(make_expr(kind))
    }

    // Parses an expression inside braces, either an object or a projection
    fn parse_brace_expr(
        &mut self,
        lhs: Option<Box<Expression>>,
    ) -> Result<Box<Expression>, String> {
        self.expect_token(Token::OpenBrace)?;

        let mut entries = Vec::new();
        loop {
            let token = self.peek_token();
            if token == &Token::CloseBrace {
                break;
            }

            let parsed_expr = self.parse_expression(0)?;

            println!("-- parse_brace_expr expr: {:?}", parsed_expr.kind);

            let attr = match parsed_expr.kind {
                ExpressionKind::BinaryOp(BinaryOp {
                    lhs,
                    operator: Operator::Colon,
                    rhs,
                }) => match lhs.kind {
                    ExpressionKind::Literal(LiteralKind::String(s)) => {
                        ast::ObjectAttribute::AliasedExpression {
                            alias: s,
                            expr: rhs,
                        }
                    }
                    _ => Err(format!("expected string literal, got {:?}", lhs))?,
                },
                _ => ObjectAttribute::Expression(parsed_expr),
            };

            entries.push(attr);

            if self.peek_token() == &Token::Comma {
                self.next_token();
            }
        }

        self.expect_token(Token::CloseBrace)?;

        let obj: Object = Object { entries };

        // none = no lhs, so we are parsing an object
        Ok(make_expr(match lhs {
            Some(lhs) => ExpressionKind::Projection(Projection {
                expr: lhs,
                object: obj,
            }),
            None => ExpressionKind::Object(obj),
        }))
    }

    // Parses an expression with an operator, either prefix or infix
    fn parse_operator(&mut self, lhs: Box<Expression>) -> Result<Box<Expression>, String> {
        println!("-- parse_operator");

        let token = self.next_token();

        let op = match parse_token_operator(&token) {
            Some(op) => op,
            None => Err(format!("unexpected token: {:?}", token))?,
        };

        let (_, rbp) = binding_power(&token, OperatorType::Infix);
        let rhs = self.parse_expression(rbp)?;

        println!("-- deets: {:?}, {:?}, {:?}", lhs, op, rhs);

        let kind = match op {
            Operator::Dot => {
                match (&lhs.kind, &rhs.kind) {
                    // When rhs is a Attr, we can convert this into an attribute access traversal
                    (_, ExpressionKind::Attr(name)) => {
                        ExpressionKind::AttributeAccess(AttributeAccess {
                            expr: lhs,
                            name: name.to_string(),
                        })
                    }

                    // todo: need to check this is valid for a dot
                    _ => ExpressionKind::BinaryOp(BinaryOp {
                        lhs,
                        operator: op,
                        rhs,
                    }),
                }
            }

            Operator::DotDot | Operator::DotDotDot => ExpressionKind::Range(Range {
                start: lhs,
                end: rhs,
                inclusive: op == Operator::DotDot,
            }),

            _ => ExpressionKind::BinaryOp(BinaryOp {
                lhs,
                operator: op,
                rhs,
            }),
        };

        println!("-- end parse_operator {:?}", kind);
        Ok(make_expr(kind))
    }

    // Parses an deref traversal expression, e.g. foo->bar, or foo->
    fn parse_arrow_deref(&mut self, lhs: Box<Expression>) -> Result<Box<Expression>, String> {
        self.expect_token(Token::Arrow)?;

        let kind = match self.peek_token().to_owned() {
            Token::Identifier(s) => {
                self.next_token();

                ExpressionKind::AttributeAccess(AttributeAccess {
                    expr: make_expr(ExpressionKind::Dereference(Dereference { expr: lhs })),
                    name: s,
                })
            }
            _ => ExpressionKind::Dereference(Dereference { expr: lhs }),
        };
        Ok(make_expr(kind))
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

fn is_postfix_operator(token: &Token) -> bool {
    match token {
        Token::EmptyBrackets => true,
        _ => false,
    }
}

fn is_constant_evaluate(expr: &Box<Expression>, lit_kind: &LiteralKind) -> bool {
    visit::ClosureVisitor::walk(&expr, |expr| match &expr.kind {
        ExpressionKind::Literal(lit) => {
            if lit.is_same_kind_as(lit_kind) {
                ControlFlow::Continue(())
            } else {
                ControlFlow::Break(())
            }
        }
        ExpressionKind::BinaryOp(BinaryOp { lhs, operator, rhs }) => {
            match operator {
                Operator::Plus | Operator::Minus | Operator::Star | Operator::Slash | Operator::Percent | Operator::DoubleStar => {
                    if is_constant_evaluate(lhs, lit_kind) && is_constant_evaluate(rhs, lit_kind) {
                        ControlFlow::Continue(())
                    } else {
                        ControlFlow::Break(())
                    }
                }
                _ => ControlFlow::Break(()),
            }
        }

        ExpressionKind::UnaryOp(UnaryOp { operator, expr }) => {
            match operator {
                Operator::Plus | Operator::Minus => {
                    if is_constant_evaluate(expr, lit_kind) {
                        ControlFlow::Continue(())
                    } else {
                        ControlFlow::Break(())
                    }
                }
                _ => ControlFlow::Break(()),
            }
        }
        _ => ControlFlow::Break(()),
    })
    .is_continue()
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
        Token::Dots(2) => Some(ast::Operator::DotDot),
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

fn make_expr(kind: ExpressionKind) -> Box<Expression> {
    Box::new(Expression { kind })
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
            Token::Colon => (1, 2), // For object access
            Token::Dot => (2, 3),   // For attribute access

            // level 1 not implemented yet
            Token::Or => (20, 21),  // Level 2, left-associative
            Token::And => (30, 31), // Level 3, left-associative
            Token::Eq | Token::NotEq | Token::Lt | Token::LtEq | Token::Gt | Token::GtEq => {
                (40, 40)
            } // Level 4, non-associative
            Token::Dots(2) | Token::Dots(3) => (50, 50), // Level 5, non-associative
            Token::Plus | Token::Minus => (60, 61), // Level 6, left-associative
            Token::Asterisk | Token::Slash | Token::Percent => (70, 71), // Level 7, left-associative
            Token::DoubleStar => (91, 90), // Level 9, right-associative
            // Level 11 not implemented yet
            _ => (0, 0),
        },
        OperatorType::Postfix => match token {
            Token::EmptyBrackets => (2, 0),
            _ => (0, 0),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_binary_expr(
        lhs: Box<Expression>,
        operator: ast::Operator,
        rhs: Box<Expression>,
    ) -> Box<Expression> {
        make_expr(ExpressionKind::BinaryOp(BinaryOp { lhs, operator, rhs }))
    }

    fn make_unary_expr(operator: ast::Operator, expr: Box<Expression>) -> Box<Expression> {
        make_expr(ExpressionKind::UnaryOp(UnaryOp { operator, expr }))
    }

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

    mod simple_expressions_tests {
        use super::*;

        parser_test!(
            attr_access: ("foo.bar", make_expr(
                ExpressionKind::AttributeAccess(AttributeAccess {
                    expr: Box::new(Expression {
                        kind: ExpressionKind::Attr("foo".to_string())
                    }),
                    name: "bar".to_string()
                }
            ))),

            attr_access_chain: ("foo.bar.baz.abc", make_expr(
                ExpressionKind::AttributeAccess(AttributeAccess {
                    expr: Box::new(Expression {
                        kind: ExpressionKind::AttributeAccess(AttributeAccess {
                            expr: Box::new(Expression {
                                kind: ExpressionKind::AttributeAccess(AttributeAccess {
                                    expr: Box::new(Expression {
                                        kind: ExpressionKind::Attr("foo".to_string())
                                    }),
                                    name: "bar".to_string()
                                })
                            }),
                            name: "baz".to_string()
                        })
                    }),
                    name: "abc".to_string()
                })
            )),

            attr_access_bracket: ("foo[\"bar\"]", make_expr(
                ExpressionKind::AttributeAccess(AttributeAccess {
                    expr: Box::new(Expression {
                        kind: ExpressionKind::Attr("foo".to_string())
                    }),
                    name: "bar".to_string()
                })
            )),

            attr_access_bracket_chain: ("foo[\"bar\"][\"baz\"][\"abc\"]", make_expr(
                ExpressionKind::AttributeAccess(AttributeAccess {
                    expr: Box::new(Expression {
                        kind: ExpressionKind::AttributeAccess(AttributeAccess {
                            expr: Box::new(Expression {
                                kind: ExpressionKind::AttributeAccess(AttributeAccess {
                                    expr: Box::new(Expression {
                                        kind: ExpressionKind::Attr("foo".to_string())
                                    }),
                                    name: "bar".to_string()
                                })
                            }),
                            name: "baz".to_string()
                        })
                    }),
                    name: "abc".to_string()
                })
            )),

            attr_access_everything: ("*.bar", make_expr(
                ExpressionKind::AttributeAccess(AttributeAccess {
                    expr: Box::new(Expression {
                        kind: ExpressionKind::Everything
                    }),
                    name: "bar".to_string()
                })
            )),

            attr_access_everything_chain: ("*.foo.bar.baz", make_expr(
                ExpressionKind::AttributeAccess(AttributeAccess {
                    expr: Box::new(Expression {
                        kind: ExpressionKind::AttributeAccess(AttributeAccess {
                            expr: Box::new(Expression {
                                kind: ExpressionKind::AttributeAccess(AttributeAccess {
                                    expr: Box::new(Expression {
                                        kind: ExpressionKind::Everything
                                    }),
                                    name: "foo".to_string()
                                })
                            }),
                            name: "bar".to_string()
                        })
                    }),
                    name: "baz".to_string()
                })
            )),

            attr_access_everything_bracket: ("*['bar']", make_expr(
                ExpressionKind::AttributeAccess(AttributeAccess {
                    expr: Box::new(Expression {
                        kind: ExpressionKind::Everything
                    }),
                    name: "bar".to_string()
                })
            )),

            attr_access_object: (
                "{\"foo\": bar}.foo.baz",
                make_expr(ExpressionKind::AttributeAccess(AttributeAccess {
                        expr: Box::new(Expression {
                            kind: ExpressionKind::AttributeAccess(AttributeAccess {
                                expr: Box::new(Expression {
                                    kind: ExpressionKind::Object(ast::Object {
                                        entries: vec![
                                            ast::ObjectAttribute::AliasedExpression {
                                                alias: "foo".to_string(),
                                                expr: Box::new(Expression {
                                                    kind: ExpressionKind::Attr("bar".to_string())
                                                })
                                            }
                                        ]
                                    })
                                }),
                                name: "foo".to_string()
                            })
                        }),
                        name: "baz".to_string()
                    })
            )),

            array_elements: ("[1, 2, 3]", make_expr(
                ExpressionKind::ArrayElements(ArrayElements {
                    elements: vec![
                        Expression {
                            kind: ExpressionKind::Literal(LiteralKind::Int64(1))
                        },
                        Expression {
                            kind: ExpressionKind::Literal(LiteralKind::Int64(2))
                        },
                        Expression {
                            kind: ExpressionKind::Literal(LiteralKind::Int64(3))
                        }
                    ]
                })
            )),

            array_postfix: ("foo[]", make_expr(
                ExpressionKind::ArrayPostfix(ArrayPostfix {
                    expr: Box::new(Expression {
                        kind: ExpressionKind::Attr("foo".to_string())
                    })
                })
            )),

            array_postfix_chain: (
                "foo[].bar[]",
                make_expr(ExpressionKind::ArrayPostfix(ArrayPostfix {
                        expr: Box::new(Expression {
                            kind: ExpressionKind::AttributeAccess(AttributeAccess {
                                expr: Box::new(Expression {
                                    kind: ExpressionKind::ArrayPostfix(ArrayPostfix {
                                        expr: Box::new(Expression {
                                            kind: ExpressionKind::Attr("foo".to_string())
                                        })
                                    })
                                }),
                                name: "bar".to_string()
                            })
                        })
                    })
                )
            ),

            filter_traversal: (
                "foo[bar == 'baz']",
                make_expr(ExpressionKind::FilterTraversal(FilterTraversal {
                        expr: Box::new(Expression {
                            kind: ExpressionKind::Attr("foo".to_string())
                        }),
                        constraint: Box::new(Expression {
                            kind: ExpressionKind::BinaryOp(BinaryOp {
                                lhs: Box::new(Expression {
                                    kind: ExpressionKind::Attr("bar".to_string())
                                }),
                                operator: Operator::Eq,
                                rhs: Box::new(Expression {
                                    kind: ExpressionKind::Literal(LiteralKind::String("baz".to_string()))
                                })
                            })
                        })
                    })
                )
            ),

            array_chained_ints: (
                "[1, 2, [3, 4, 5]][3][0]",
                make_expr(ExpressionKind::ElementAccess(ElementAccess {
                        expr: Box::new(Expression {
                            kind: ExpressionKind::ElementAccess(ElementAccess {
                                expr: Box::new(Expression {
                                    kind: ExpressionKind::ArrayElements(ArrayElements {
                                        elements: vec![
                                            Expression {
                                                kind: ExpressionKind::Literal(LiteralKind::Int64(1))
                                            },
                                            Expression {
                                                kind: ExpressionKind::Literal(LiteralKind::Int64(2))
                                            },
                                            Expression {
                                                kind: ExpressionKind::ArrayElements(ArrayElements {
                                                    elements: vec![
                                                        Expression {
                                                            kind: ExpressionKind::Literal(LiteralKind::Int64(3))
                                                        },
                                                        Expression {
                                                            kind: ExpressionKind::Literal(LiteralKind::Int64(4))
                                                        },
                                                        Expression {
                                                            kind: ExpressionKind::Literal(LiteralKind::Int64(5))
                                                        }
                                                    ]
                                                })
                                            }
                                        ]
                                    })
                                }),
                                index: Box::new(Expression {
                                    kind: ExpressionKind::Literal(LiteralKind::Int64(3))
                                })
                            }),
                        }),
                        index: Box::new(Expression {
                            kind: ExpressionKind::Literal(LiteralKind::Int64(0))
                        })
                    })
                )
            ),

            array_bool: (
                "[true, false, null][0]",
                make_expr(ExpressionKind::ElementAccess(ElementAccess {
                        expr: Box::new(Expression {
                            kind: ExpressionKind::ArrayElements(ArrayElements {
                                elements: vec![
                                    Expression {
                                        kind: ExpressionKind::Literal(LiteralKind::Boolean(true))
                                    },
                                    Expression {
                                        kind: ExpressionKind::Literal(LiteralKind::Boolean(false))
                                    },
                                    Expression {
                                        kind: ExpressionKind::Literal(LiteralKind::Null)
                                    }
                                ]
                            })
                        }),
                        index: Box::new(Expression {
                            kind: ExpressionKind::Literal(LiteralKind::Int64(0))
                        })
                    })
                )
            ),

            object: (
                "{\"foo\": bar, \"baz\": 2}",
                make_expr(ExpressionKind::Object(Object {
                        entries: vec![
                            ObjectAttribute::AliasedExpression {
                                alias: "foo".to_string(),
                                expr: Box::new(Expression {
                                    kind: ExpressionKind::Attr("bar".to_string())
                                })
                            },
                            ObjectAttribute::AliasedExpression {
                                alias: "baz".to_string(),
                                expr: Box::new(Expression {
                                    kind: ExpressionKind::Literal(LiteralKind::Int64(2))
                                })
                            },
                        ]
                    })
                )
            ),

            object_nested: (
                "{\"foo\": {\"bar\": 2}}",
                make_expr(ExpressionKind::Object(Object {
                        entries: vec![
                            ObjectAttribute::AliasedExpression {
                                alias: "foo".to_string(),
                                expr: Box::new(Expression {
                                    kind: ExpressionKind::Object(Object {
                                        entries: vec![
                                            ObjectAttribute::AliasedExpression {
                                                alias: "bar".to_string(),
                                                expr: Box::new(Expression {
                                                    kind: ExpressionKind::Literal(LiteralKind::Int64(2))
                                                })
                                            }
                                        ]
                                    })
                                })
                            }
                        ]
                    })
                )
            ),

            dereference: (
                "foo->bar",
                make_expr(ExpressionKind::AttributeAccess(AttributeAccess {
                        expr: Box::new(Expression {
                            kind: ExpressionKind::Dereference(Dereference {
                                expr: Box::new(Expression {
                                    kind: ExpressionKind::Attr("foo".to_string())
                                })
                            })
                        }),
                        name: "bar".to_string()
                    })
                )
            ),

            dereference_nested_array: (
                "bar[]->meta->title.en",
                make_expr(ExpressionKind::AttributeAccess(AttributeAccess {
                        expr: Box::new(Expression {
                            kind: ExpressionKind::AttributeAccess(AttributeAccess {
                                expr: Box::new(Expression {
                                    kind: ExpressionKind::Dereference(Dereference {
                                        expr: Box::new(Expression {
                                            kind: ExpressionKind::AttributeAccess(AttributeAccess {
                                                expr: Box::new(Expression {
                                                    kind: ExpressionKind::Dereference(Dereference {
                                                        expr: Box::new(Expression {
                                                            kind: ExpressionKind::ArrayPostfix(ArrayPostfix {
                                                                expr: Box::new(Expression {
                                                                    kind: ExpressionKind::Attr("bar".to_string())
                                                                })
                                                            })
                                                        })
                                                    })
                                                }),
                                                name: "meta".to_string()
                                            })
                                        })
                                    })
                                }),
                                name: "title".to_string()
                            })
                        }),
                        name: "en".to_string()
                    })
                )
            ),

            dereference_projection: (
                "foo->{bar, baz}",
                make_expr(ExpressionKind::Projection(Projection {
                        expr: Box::new(Expression {
                            kind: ExpressionKind::Dereference(Dereference {
                                expr: Box::new(Expression {
                                    kind: ExpressionKind::Attr("foo".to_string())
                                })
                            })
                        }),
                        object: ast::Object {
                            entries: vec![
                                ast::ObjectAttribute::Expression(Box::new(Expression {
                                    kind: ExpressionKind::Attr("bar".to_string())
                                })),
                                ast::ObjectAttribute::Expression(Box::new(Expression {
                                    kind: ExpressionKind::Attr("baz".to_string())
                                })),
                            ]
                        }
                    })
                )
            ),

            dereference_projection_attr_access: (
                "foo->{bar, baz}.bar",
                make_expr(ExpressionKind::AttributeAccess(AttributeAccess {
                        expr: Box::new(Expression {
                            kind: ExpressionKind::Projection(Projection {
                                expr: Box::new(Expression {
                                    kind: ExpressionKind::Dereference(Dereference {
                                        expr: Box::new(Expression {
                                            kind: ExpressionKind::Attr("foo".to_string())
                                        })
                                    })
                                }),
                                object: ast::Object {
                                    entries: vec![
                                        ast::ObjectAttribute::Expression(Box::new(Expression {
                                            kind: ExpressionKind::Attr("bar".to_string())
                                        })),
                                        ast::ObjectAttribute::Expression(Box::new(Expression {
                                            kind: ExpressionKind::Attr("baz".to_string())
                                        })),
                                    ]
                                }
                            })
                        }),
                        name: "bar".to_string()
                    })
                )
            ),

            ranged_slice_incl: (
                "foo[-1..3]",
                make_expr(ExpressionKind::SliceTraversal(SliceTraversal {
                        range: ast::Range {
                            start: make_unary_expr(Operator::Minus, make_expr(ExpressionKind::Literal(LiteralKind::Int64(1)))),
                            end: make_expr(ExpressionKind::Literal(LiteralKind::Int64(3))),
                            inclusive: true
                        }
                    })
                )
            ),

            ranged_slice_excl: (
                "foo[1...-3]",
                make_expr(ExpressionKind::SliceTraversal(SliceTraversal {
                        range: ast::Range {
                            start: make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                            end: make_unary_expr(Operator::Minus, make_expr(ExpressionKind::Literal(LiteralKind::Int64(3)))),
                            inclusive: false
                        }
                    })
                )
            ),

            ranged_filter: (
                "foo[bar == foo..bar]",
                make_expr(ExpressionKind::FilterTraversal(FilterTraversal {
                        expr: make_expr(ExpressionKind::Attr("foo".to_string())),
                        constraint: make_binary_expr(
                            make_expr(ExpressionKind::Attr("bar".to_string())),
                            Operator::Eq,
                            make_expr(ExpressionKind::Range(Range {
                                start: make_expr(ExpressionKind::Attr("foo".to_string())),
                                end: make_expr(ExpressionKind::Attr("bar".to_string())),
                                inclusive: true
                            }))
                        )
                    })
                )
            ),
        );
    }

    mod precedence_associativity_tests {
        use super::*;

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
                make_binary_expr(
                    make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true))),
                        Operator::Or,
                        make_expr(ExpressionKind::Literal(LiteralKind::Boolean(false)))
                    ),
                    Operator::Or,
                    make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true)))
                )
            ),

            level_3: (
                "true && false && true",
                make_binary_expr(
                    make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true))),
                        Operator::And,
                        make_expr(ExpressionKind::Literal(LiteralKind::Boolean(false)))
                    ),
                    Operator::And,
                    make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true)))
                )
            ),

            level_3_2: (
                "true || false && false || true",
                make_binary_expr(
                    make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true))),
                        Operator::Or,
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Boolean(false))),
                            Operator::And,
                            make_expr(ExpressionKind::Literal(LiteralKind::Boolean(false)))
                        )
                    ),
                    Operator::Or,
                    make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true)))
                )
            ),

            level_3_2a: (
                "true && false || false && true",
                make_binary_expr(
                    make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true))),
                        Operator::And,
                        make_expr(ExpressionKind::Literal(LiteralKind::Boolean(false)))
                    ),
                    Operator::Or,
                    make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Boolean(false))),
                        Operator::And,
                        make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true)))
                    )
                )
            ),

            level_4_ands: (
                "1 == 2 && 3 != 4 && 5 > 6 && 7 >= 8 && 9 < 10 && 11 <= 12",
                make_binary_expr(
                    make_binary_expr(
                        make_binary_expr(
                            make_binary_expr(
                                make_binary_expr(
                                    make_binary_expr(
                                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                                        Operator::Eq,
                                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(2)))
                                    ),
                                    Operator::And,
                                    make_binary_expr(
                                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(3))),
                                        Operator::NotEq,
                                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(4)))
                                    )
                                ),
                                Operator::And,
                                make_binary_expr(
                                    make_expr(ExpressionKind::Literal(LiteralKind::Int64(5))),
                                    Operator::Gt,
                                    make_expr(ExpressionKind::Literal(LiteralKind::Int64(6)))
                                )
                            ),
                            Operator::And,
                            make_binary_expr(
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(7))),
                                Operator::GtEq,
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(8)))
                            )
                        ),
                        Operator::And,
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(9))),
                            Operator::Lt,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(10)))
                        )
                    ),
                    Operator::And,
                    make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(11))),
                        Operator::LtEq,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(12)))
                    )
                ),
            ),

            level_4_ors: (
                "1 == 2 || 3 != 4 || 5 > 6 || 7 >= 8 || 9 < 10 || 11 <= 12",
                make_binary_expr(
                    make_binary_expr(
                        make_binary_expr(
                            make_binary_expr(
                                make_binary_expr(
                                    make_binary_expr(
                                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                                        Operator::Eq,
                                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(2)))
                                    ),
                                    Operator::Or,
                                    make_binary_expr(
                                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(3))),
                                        Operator::NotEq,
                                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(4)))
                                    )
                                ),
                                Operator::Or,
                                make_binary_expr(
                                    make_expr(ExpressionKind::Literal(LiteralKind::Int64(5))),
                                    Operator::Gt,
                                    make_expr(ExpressionKind::Literal(LiteralKind::Int64(6)))
                                )
                            ),
                            Operator::Or,
                            make_binary_expr(
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(7))),
                                Operator::GtEq,
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(8)))
                            )
                        ),
                        Operator::Or,
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(9))),
                            Operator::Lt,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(10)))
                        )
                    ),
                    Operator::Or,
                    make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(11))),
                        Operator::LtEq,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(12)))
                    )
                ),
            ),

            level_4_ands_ors: (
                "1 == 2 && 3 != 4 || 5 > 6 && 7 >= 8 || 9 < 10 && 11 <= 12",
                make_binary_expr(
                    make_binary_expr(
                        make_binary_expr(
                            make_binary_expr(
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                                Operator::Eq,
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(2))
                            )),
                            Operator::And,
                            make_binary_expr(
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(3))),
                                Operator::NotEq,
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(4))
                            )
                        )),
                        Operator::Or,
                        make_binary_expr(
                            make_binary_expr(
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(5))),
                                Operator::Gt,
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(6))
                            )),
                            Operator::And,
                            make_binary_expr(
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(7))),
                                Operator::GtEq,
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(8)))
                            )
                        )
                    ),
                    Operator::Or,
                    make_binary_expr(
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(9))),
                            Operator::Lt,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(10))
                        )),
                        Operator::And,
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(11))),
                            Operator::LtEq,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(12)))
                        )
                    )
                ),
            ),

            level_5: (
                "1 + 2..5",
                make_expr(ExpressionKind::Range(Range {
                    start: make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                        Operator::Plus,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(2)))
                    ),
                    end: make_expr(ExpressionKind::Literal(LiteralKind::Int64(5))),
                    inclusive: true
                })),
            ),

            level_5a: (
                "1 + 2...5",
                make_expr(ExpressionKind::Range(Range {
                    start: make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                        Operator::Plus,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(2)))
                    ),
                    end: make_expr(ExpressionKind::Literal(LiteralKind::Int64(5))),
                    inclusive: false
                })),
            ),

            level_6: (
                "1 + 2 - 3 + 4",
                make_binary_expr(
                    make_binary_expr(
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                            Operator::Plus,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(2))
                        )),
                        Operator::Minus,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(3))
                    )),
                    Operator::Plus,
                    make_expr(ExpressionKind::Literal(LiteralKind::Int64(4)))
                )
            ),

            level_6_2: (
                "1 + 2 || 3 - 4 && 5 + 6",
                make_binary_expr(
                    make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                        Operator::Plus,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(2)))
                    ),
                    Operator::Or,
                    make_binary_expr(
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(3))),
                            Operator::Minus,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(4)))
                        ),
                        Operator::And,
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(5))),
                            Operator::Plus,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(6)))
                        )
                    )
                ),
            ),

            level_7: (
                "1 * 2 / 3 % 4",
                make_binary_expr(
                    make_binary_expr(
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                            Operator::Star,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(2)))
                        ),
                        Operator::Slash,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(3)))
                    ),
                    Operator::Percent,
                    make_expr(ExpressionKind::Literal(LiteralKind::Int64(4)))
                ),
            ),

            level_7_6: (
                "1 * 2 / 3 + 4 * 5 % 6",
                make_binary_expr(
                    make_binary_expr(
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                            Operator::Star,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(2)))
                        ),
                        Operator::Slash,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(3)))
                    ),
                    Operator::Plus,
                    make_binary_expr(
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(4))),
                            Operator::Star,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(5)))
                        ),
                        Operator::Percent,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(6)))
                    )
                )
            ),

            level_7_2_3: (
                "1 * 2 || 3 / 4 && 5 * 6",
                make_binary_expr(
                    make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                        Operator::Star,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(2)))
                    ),
                    Operator::Or,
                    make_binary_expr(
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(3))),
                            Operator::Slash,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(4)))
                        ),
                        Operator::And,
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(5))),
                            Operator::Star,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(6)))
                        )
                    )
                ),
            ),

            level_8: (
                "+1 - 2",
                make_binary_expr(
                    make_unary_expr(
                        Operator::Plus,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))
                    )),
                    Operator::Minus,
                    make_expr(ExpressionKind::Literal(LiteralKind::Int64(2)))
                )
            ),

            level_8_7: (
                "+1 * 2 - -3 / 4",
                make_binary_expr(
                    make_binary_expr(
                        make_unary_expr(
                            Operator::Plus,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))
                        )),
                        Operator::Star,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(2)))
                    ),
                    Operator::Minus,
                    make_binary_expr(
                        make_unary_expr(
                            Operator::Minus,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(3))
                        )),
                        Operator::Slash,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(4)))
                    )
                )
            ),

            level_8_2_3: (
                "+1 || 2 - -3 && 4",
                make_binary_expr(
                    make_unary_expr(
                        Operator::Plus,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))
                    )),
                    Operator::Or,
                    make_binary_expr(
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(2))),
                            Operator::Minus,
                            make_unary_expr(
                                Operator::Minus,
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(3)))
                            )
                        ),
                        Operator::And,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(4)))
                    )
                )
            ),

            level_9: (
                "1 ** 2 ** 3",
                make_binary_expr(
                    make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                    Operator::DoubleStar,
                    make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(2))),
                        Operator::DoubleStar,
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(3)))
                    )
                )
            ),

            level_9_8: (
                "1 ** +2 ** -3",
                make_binary_expr(
                    make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                    Operator::DoubleStar,
                    make_unary_expr(
                        Operator::Plus,
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(2))),
                            Operator::DoubleStar,
                            make_unary_expr(
                                Operator::Minus,
                                make_expr(ExpressionKind::Literal(LiteralKind::Int64(3)))
                            )
                        )
                    ),
                ),
            ),

            level_9_8_2: (
                "1 ** +2 || -3 ** 4",
                make_binary_expr(
                    make_binary_expr(
                        make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
                        Operator::DoubleStar,
                        make_unary_expr(
                            Operator::Plus,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(2))
                        )),
                    ),
                    Operator::Or,
                    make_unary_expr(
                        Operator::Minus,
                        make_binary_expr(
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(3))),
                            Operator::DoubleStar,
                            make_expr(ExpressionKind::Literal(LiteralKind::Int64(4))
                        )),
                    ),
                ),
            ),

            level_10: (
                "!true",
                make_unary_expr(
                    Operator::Not,
                    make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true)))
                )
            ),

            level_10_2_3: (
                "!true || !false && !true || true",
                make_binary_expr(
                    make_binary_expr(
                        make_unary_expr(
                            Operator::Not,
                            make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true)))
                        ),
                        Operator::Or,
                        make_binary_expr(
                            make_unary_expr(
                                Operator::Not,
                                make_expr(ExpressionKind::Literal(LiteralKind::Boolean(false)))
                            ),
                            Operator::And,
                            make_unary_expr(
                                Operator::Not,
                                make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true)))
                            ),
                        ),
                    ),
                    Operator::Or,
                    make_expr(ExpressionKind::Literal(LiteralKind::Boolean(true)))
                ),
            ),
        );
    }

    mod misc_tests {
        use super::*;

        parser_test!(
            projection_join: (
                "{\"everything\": *[_type == 'foo']}",
                make_expr(ExpressionKind::Object(Object {
                    entries: vec![
                        ObjectAttribute::AliasedExpression {
                            alias: "everything".to_string(),
                            expr: make_expr(
                                ExpressionKind::FilterTraversal(FilterTraversal {
                                    expr: make_expr(ExpressionKind::Everything),
                                    constraint: make_binary_expr(
                                        make_expr(ExpressionKind::Attr("_type".to_string())),
                                        Operator::Eq,
                                        make_expr(ExpressionKind::Literal(LiteralKind::String("foo".to_string())))
                                    )
                                })
                            )
                        }
                    ]
                })
            )),

            projection_nested: (
                r#"
                    {
                        "everything": *[_type == 'foo'] {
                            "metadata": bar[]->meta->title.en,
                            "a": 1,
                            "b": {
                                "c": c->{
                                    "d": d[]
                                }
                            },
                            empty
                        }
                    }
                "#,
                make_expr(ExpressionKind::Object(Object {
                    entries: vec![
                        ObjectAttribute::AliasedExpression {
                            alias: "everything".to_string(),
                            expr: Box::new(Expression {
                                kind: ExpressionKind::Projection(Projection {
                                    expr: Box::new(Expression {
                                        kind: ExpressionKind::FilterTraversal(FilterTraversal {
                                            expr: Box::new(Expression {
                                                kind: ExpressionKind::Everything
                                            }),
                                            constraint: Box::new(Expression {
                                                kind: ExpressionKind::BinaryOp(BinaryOp {
                                                    lhs: Box::new(Expression {
                                                        kind: ExpressionKind::Attr("_type".to_string())
                                                    }),
                                                    operator: Operator::Eq,
                                                    rhs: Box::new(Expression {
                                                        kind: ExpressionKind::Literal(LiteralKind::String("foo".to_string()))
                                                    })
                                                })
                                            })
                                        })
                                    }),
                                    object: ast::Object {
                                        entries: vec![
                                            ast::ObjectAttribute::AliasedExpression {
                                                alias: "metadata".to_string(),
                                                expr: make_expr(ExpressionKind::AttributeAccess(AttributeAccess {
                                                    expr: Box::new(Expression {
                                                        kind: ExpressionKind::AttributeAccess(AttributeAccess {
                                                            expr: Box::new(Expression {
                                                                kind: ExpressionKind::Dereference(Dereference {
                                                                    expr: Box::new(Expression {
                                                                        kind: ExpressionKind::AttributeAccess(AttributeAccess {
                                                                            expr: Box::new(Expression {
                                                                                kind: ExpressionKind::Dereference(Dereference {
                                                                                    expr: Box::new(Expression {
                                                                                        kind: ExpressionKind::ArrayPostfix(ArrayPostfix {
                                                                                            expr: Box::new(Expression {
                                                                                                kind: ExpressionKind::Attr("bar".to_string())
                                                                                            })
                                                                                        })
                                                                                    })
                                                                                })
                                                                            }),
                                                                            name: "meta".to_string()
                                                                        })
                                                                    })
                                                                })
                                                            }),
                                                            name: "title".to_string()
                                                        })
                                                    }),
                                                    name: "en".to_string()
                                                }))
                                            },
                                            ast::ObjectAttribute::AliasedExpression {
                                                alias: "a".to_string(),
                                                expr: make_expr(ExpressionKind::Literal(LiteralKind::Int64(1)))
                                            },
                                            ast::ObjectAttribute::AliasedExpression {
                                                alias: "b".to_string(),
                                                expr: make_expr(ExpressionKind::Object(Object {
                                                    entries: vec![
                                                        ObjectAttribute::AliasedExpression {
                                                            alias: "c".to_string(),
                                                            expr: make_expr(ExpressionKind::Projection(Projection {
                                                                expr: make_expr(ExpressionKind::Dereference(Dereference {
                                                                    expr: make_expr(ExpressionKind::Attr("c".to_string()))
                                                                })),
                                                                object: ast::Object {
                                                                    entries: vec![
                                                                        ast::ObjectAttribute::AliasedExpression {
                                                                            alias: "d".to_string(),
                                                                            expr: make_expr(ExpressionKind::ArrayPostfix(ArrayPostfix {
                                                                                expr: make_expr(ExpressionKind::Attr("d".to_string()))
                                                                            }))
                                                                        }
                                                                    ]
                                                                }
                                                            }))
                                                        }
                                                    ]
                                                })),
                                            },
                                            ast::ObjectAttribute::Expression(make_expr(ExpressionKind::Attr("empty".to_string())))
                                        ]
                                    }
                                })
                            })
                        },
                    ]
                })
            )),
        );
    }

    #[test]
    fn test_is_constant_evaluate() {
        let expr = make_binary_expr(
            make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
            Operator::Plus,
            make_expr(ExpressionKind::Literal(LiteralKind::Int64(2))),
        );
        assert_eq!(is_constant_evaluate(&expr, &LiteralKind::Int64(0)), true);

        let expr = make_binary_expr(
            make_expr(ExpressionKind::Literal(LiteralKind::String("foo".to_string()))),
            Operator::Plus,
            make_expr(ExpressionKind::Literal(LiteralKind::String("bar".to_string()))),
        );
        assert_eq!(is_constant_evaluate(&expr, &LiteralKind::String("".to_string())), true);

        let expr = make_binary_expr(
            make_expr(ExpressionKind::Literal(LiteralKind::Int64(1))),
            Operator::Plus,
            make_expr(
                ExpressionKind::Dereference(Dereference {
                    expr: Box::new(Expression {
                        kind: ExpressionKind::Attr("foo".to_string())
                    })
                })
            ),
        );
        assert_eq!(is_constant_evaluate(&expr, &LiteralKind::Int64(0)), false);
    }

    #[test]
    fn test_print_output() {
        let lex: Lexer<'_> = Lexer::new(
            r#"
            {
                "everything": *[_type == 'foo'] {
                    "metadata": bar[]->meta->title.en,
                    "a": 1,
                    "b": {
                        "c": c->{
                            "d": d[]
                        }
                    },
                    empty
                }
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
