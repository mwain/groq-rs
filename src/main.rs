use groqparser::lexer::*;
use groqparser::parser::*;

fn main() {
    let lex: Lexer<'_> = Lexer::new(
        r#"
        *[_type == "person" && foo.bar[].score > 10]{
            name,
            "over18": age >= 18,
            "join": *[_type == "join" && _id == ^.someId] {
                "joinName": name,
                "joinAge": age
            },
            "array": [foo, bar, "baz", 2],
            "ref": abc->{name, age},
        }
    "#,
    );

    // Parser::new(lex).parse().
    match Parser::new(lex).parse() {
        Ok(ast) => println!("{:#?}", ast),
        Err(e) => println!("{}", e),
    }
}
