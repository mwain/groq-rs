use core::iter::Peekable;
use core::str::Chars;

// TODO: Maybe... return Result<Token, Err> instead of Token::Unknown
// TODO: Implement unicode escape in strings
// TODO: Need to confirm skip_whitespace() conforms to the spec
// TODO: Returning lexer errors instead of Token::Unknown
// TODO: Maybe... return position of token in input?

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Not a real token, but a signal that we've reached the end of the input.
    EOF,

    // Identifiers are used to name entities such as parameters, attributes and functions
    Identifier(String),

    // Numbers are used to represent numeric values, E.g 123, 3.14, 3.14e-10, .5
    Number(String),

    // Single Dot
    Dot,

    // Multiple Dots
    Dots(u8),

    // "|"
    Pipe,

    // "/"
    Slash,

    // "["
    OpenBracket,

    // "]"
    CloseBracket,

    // "("
    OpenParen,

    // ")"
    CloseParen,

    // "{"
    OpenBrace,

    // "}"
    CloseBrace,

    // "*"
    Asterisk,

    // "&&"
    And,

    // "||"
    Or,

    // "!"
    Not,

    // "=="
    Eq,

    // "!="
    NotEq,

    // "<"
    Lt,

    // "<="
    LtEq,

    // ">"
    Gt,

    // ">="
    GtEq,

    // "+"
    Plus,

    // "-"
    Minus,

    // "%"
    Percent,

    // "**"
    DoubleStar,

    // "->"
    Arrow,

    // ":"
    Colon,

    // ","
    Comma,

    // "::"
    DoubleColon,

    // Single or double quoted string
    String(String),

    EmptyBrackets,

    // A character that we don't recognize
    Unknown,
}

pub struct Lexer<'a> {
    chars: Peekable<Chars<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars().peekable(),
        }
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        match self.chars.next() {
            Some(c) => match c {
                '/' => match self.chars.peek() {
                    Some('/') => {
                        self.skip_comment();

                        // Advance to the next token.
                        self.next_token()
                    }
                    _ => Token::Slash,
                },

                c if is_identifier_start(c) => self.identifier(&c),
                '0'..='9' => self.number(&c),
                '.' => self.dot(&c),
                c if is_operator_start(c) => self.operator(&c),
                '"' | '\'' => self.string(&c),

                '*' => Token::Asterisk,
                '[' => Token::OpenBracket,
                ']' => Token::CloseBracket,
                '(' => Token::OpenParen,
                ')' => Token::CloseParen,
                '{' => Token::OpenBrace,
                '}' => Token::CloseBrace,
                '|' => Token::Pipe,
                ':' => {
                    if Some(&':') == self.chars.peek() {
                        self.chars.next();
                        Token::DoubleColon
                    } else {
                        Token::Colon
                    }
                }
                ',' => Token::Comma,

                _ => Token::Unknown,
            },
            None => Token::EOF,
        }
    }

    fn skip_whitespace(&mut self) {
        self.skip_while(char::is_whitespace);
    }

    fn skip_comment(&mut self) {
        self.skip_while(|c| c != '\n');
    }

    fn skip_while(&mut self, predicate: impl Fn(char) -> bool) {
        while let Some(&c) = self.chars.peek() {
            if predicate(c) {
                self.chars.next();
            } else {
                break;
            }
        }
    }

    fn peek_nth(&mut self, n: usize) -> Option<char> {
        self.chars.clone().nth(n)
    }

    fn identifier(&mut self, first_ch: &char) -> Token {
        let mut ident = first_ch.to_string();
        ident.push_str(&take_while(&mut self.chars, is_identifier_char));

        Token::Identifier(ident)
    }

    fn number(&mut self, first_digit: &char) -> Token {
        let mut number = first_digit.to_string();
        number += take_while(&mut self.chars, |c| c.is_ascii_digit()).as_str();

        if Some('.') == self.peek_nth(0) && Some('.') == self.peek_nth(1) {
            // Probably a range, e.g. 1..2
            return Token::Number(number);
        }

        if Some('.') == self.peek_nth(0) {
            number.push(self.chars.next().unwrap());
            number += take_while(&mut self.chars, |c| c.is_ascii_digit()).as_str();
        }

        let mut exponent = String::new();
        if let Some(&'e') | Some(&'E') = self.chars.peek() {
            // Clone the chars iterator while we parse the exponent, as it may not be valid
            let mut chars_clone = self.chars.clone();

            exponent.push(chars_clone.next().unwrap());

            if let Some(&'+') | Some(&'-') = chars_clone.peek() {
                exponent.push(chars_clone.next().unwrap());
            }

            // When next char is a digit, its a valid exponent, consume all digits
            match chars_clone.peek() {
                Some(&c) if c.is_ascii_digit() => {
                    for _ in 0..exponent.len() {
                        self.chars.next();
                    }

                    number += exponent.as_str();
                    number += take_while(&mut self.chars, |c| c.is_ascii_digit()).as_str();
                }
                // Not a valid exponent, return the number as is
                _ => return Token::Number(number),
            }
        }

        Token::Number(number)
    }

    fn dot(&mut self, first_dot: &char) -> Token {
        let mut dots = first_dot.to_string();
        dots += take_while(&mut self.chars, |c| c == '.').as_str();

        match dots.len() {
            1 => Token::Dot,
            2..=3 => Token::Dots(dots.len() as u8),
            _ => Token::Unknown,
        }
    }

    fn operator(&mut self, first_ch: &char) -> Token {
        match first_ch {
            '&' => match self.chars.peek() {
                Some(&'&') => {
                    self.chars.next();
                    Token::And
                }
                _ => Token::Unknown,
            },

            '|' => match self.chars.peek() {
                Some(&'|') => {
                    self.chars.next();
                    Token::Or
                }
                _ => Token::Pipe,
            },

            '!' => match self.chars.peek() {
                Some(&'=') => {
                    self.chars.next();
                    Token::NotEq
                }
                _ => Token::Not,
            },

            '=' => match self.chars.peek() {
                Some(&'=') => {
                    self.chars.next();
                    Token::Eq
                }
                _ => Token::Unknown,
            },

            '<' => match self.chars.peek() {
                Some(&'=') => {
                    self.chars.next();
                    Token::LtEq
                }
                _ => Token::Lt,
            },

            '>' => match self.chars.peek() {
                Some(&'=') => {
                    self.chars.next();
                    Token::GtEq
                }
                _ => Token::Gt,
            },

            '-' => match self.chars.peek() {
                Some(&'>') => {
                    self.chars.next();
                    Token::Arrow
                }
                _ => Token::Minus,
            },

            '+' => Token::Plus,

            '*' => match self.chars.peek() {
                Some(&'*') => {
                    self.chars.next();
                    Token::DoubleStar
                }
                _ => Token::Asterisk,
            },

            '/' => Token::Slash,

            '%' => Token::Percent,

            _ => Token::Unknown,
        }
    }

    fn string(&mut self, first_quote: &char) -> Token {
        let mut string = String::new();

        while let Some(&c) = self.chars.peek() {
            match c {
                _ if c == *first_quote => {
                    self.chars.next();
                    return Token::String(string);
                }
                '\\' => {
                    self.chars.next();

                    match self.chars.peek() {
                        Some(&ech) => match ech {
                            '\'' | '"' | '\\' | '/' => {
                                string.push(ech);
                                self.chars.next();
                            }
                            'b' => {
                                string.push('\u{0008}');
                                self.chars.next();
                            } // Backspace
                            'f' => {
                                string.push('\u{000C}');
                                self.chars.next();
                            } // Form feed
                            'n' => {
                                string.push('\u{000A}');
                                self.chars.next();
                            } // Newline
                            'r' => {
                                string.push('\u{000D}');
                                self.chars.next();
                            } // Carriage return
                            't' => {
                                string.push('\u{0009}');
                                self.chars.next();
                            } // Tab
                            'u' => {
                                self.chars.next();
                            }
                            _ => return Token::Unknown,
                        },
                        None => {
                            // we advance the iterator, so we need to break the loop
                            self.chars.next();
                        }
                    };
                }
                _ => {
                    self.chars.next();
                    string.push(c);
                }
            }
        }

        Token::Unknown
    }
}

fn is_identifier_start(c: char) -> bool {
    c.is_ascii_lowercase() || c.is_ascii_uppercase() || c == '_'
}

fn is_identifier_char(c: char) -> bool {
    c.is_ascii_lowercase() || c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_'
}

fn is_operator_start(c: char) -> bool {
    matches!(
        c,
        '&' | '|' | '!' | '=' | '<' | '>' | '+' | '-' | '*' | '/' | '%'
    )
}

fn take_while(chars: &mut Peekable<Chars<'_>>, predicate: impl Fn(char) -> bool) -> String {
    let mut str = String::new();

    while let Some(&c) = chars.peek() {
        if predicate(c) {
            str.push(c);
            chars.next();
        } else {
            break;
        }
    }

    str
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_all_tokens() {
        let query = r#"
            // Comment
            *[_type == "foo" && _other != 'b a r ' || a > 1 && b >=  0.1 || c < 3.14e+123 && "d" <= 'aaaa'] | order(some_field desc) [0..10] {
                "a": 1,
                "b": 2.0,
                "c": true,
            }
        "#;

        let expected = vec![
            Token::Asterisk,
            Token::OpenBracket,
            Token::Identifier("_type".to_string()),
            Token::Eq,
            Token::String("foo".to_string()),
            Token::And,
            Token::Identifier("_other".to_string()),
            Token::NotEq,
            Token::String("b a r ".to_string()),
            Token::Or,
            Token::Identifier("a".to_string()),
            Token::Gt,
            Token::Number("1".to_string()),
            Token::And,
            Token::Identifier("b".to_string()),
            Token::GtEq,
            Token::Number("0.1".to_string()),
            Token::Or,
            Token::Identifier("c".to_string()),
            Token::Lt,
            Token::Number("3.14e+123".to_string()),
            Token::And,
            Token::String("d".to_string()),
            Token::LtEq,
            Token::String("aaaa".to_string()),
            Token::CloseBracket,
            Token::Pipe,
            Token::Identifier("order".to_string()),
            Token::OpenParen,
            Token::Identifier("some_field".to_string()),
            Token::Identifier("desc".to_string()),
            Token::CloseParen,
            Token::OpenBracket,
            Token::Number("0".to_string()),
            Token::Dots(2),
            Token::Number("10".to_string()),
            Token::CloseBracket,
            Token::OpenBrace,
            Token::String("a".to_string()),
            Token::Colon,
            Token::Number("1".to_string()),
            Token::Comma,
            Token::String("b".to_string()),
            Token::Colon,
            Token::Number("2.0".to_string()),
            Token::Comma,
            Token::String("c".to_string()),
            Token::Colon,
            Token::Identifier("true".to_string()),
            Token::Comma,
            Token::CloseBrace,
            Token::EOF,
        ];

        let mut lex = Lexer::new(query);

        for expected_token in expected {
            let token = lex.next_token();
            assert_eq!(token, expected_token);
        }
    }
}
