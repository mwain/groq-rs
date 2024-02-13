#[derive(Debug, PartialEq)]
pub enum Expression {

    // Traversals...
    // https://sanity-io.github.io/GROQ/GROQ-1.revision1/#TraversalExpression


    // https://sanity-io.github.io/GROQ/GROQ-1.revision1/#AttributeAccess
    AttributeAccess {
        expr: Box<Expression>,
        name: String,
    },

    // https://sanity-io.github.io/GROQ/GROQ-1.revision1/#Dereference
    Dereference {
        expr: Box<Expression>,
    },

    // https://sanity-io.github.io/GROQ/GROQ-1.revision1/#Slice
    SliceTraversal {
        range: Range,
    },

    // https://sanity-io.github.io/GROQ/GROQ-1.revision1/#Filter
    FilterTraversal {
        expr: Box<Expression>,
        constraint: Box<Expression>,
    },

    // https://sanity-io.github.io/GROQ/GROQ-1.revision1/#ElementAccess
    ElementAccess {
        expr: Box<Expression>,
        index: Box<Expression>,
    },

    // https://sanity-io.github.io/GROQ/GROQ-1.revision1/#ArrayPostfix
    ArrayPostfix {
        expr: Box<Expression>,
    },

    // https://sanity-io.github.io/GROQ/GROQ-1.revision1/#Projection
    Projection {
        expr: Box<Expression>,
        object: Object,
    },

    // https://sanity-io.github.io/GROQ/GROQ-1.revision1/#ArrayElements
    ArrayElements {
        elements: Vec<Expression>,
    },

    Object(Object),

    BinaryOp {
        lhs: Box<Expression>,
        operator: Operator,
        rhs: Box<Expression>,
    },

    UnaryOp {
        operator: Operator,
        expr: Box<Expression>,
    },

    Literal(LiteralKind),
    This,
    Everything,
    Parent,
    Attr(String),
}

// https://sanity-io.github.io/GROQ/GROQ-1.revision1/#TraversalExpression
#[derive(Debug, PartialEq)]
pub enum TraversalExpression {

}

#[derive(Debug, PartialEq)]
pub enum LiteralKind {
    Null,
    Boolean(bool),
    Int64(i64),
    Float64(f64),
    String(String),
}

#[derive(Debug, PartialEq)]
pub struct Range {
    pub start: Box<Expression>,
    pub  end: Box<Expression>,
    pub inclusive: bool,
}

// https://sanity-io.github.io/GROQ/GROQ-1.revision1/#sec-Object
#[derive(Debug, PartialEq)]
pub struct Object {
    pub entries: Vec<ObjectAttribute>,
}

#[derive(Debug, PartialEq)]
pub enum ObjectAttribute {
    Expression(Box<Expression>),
    AliasedExpression {
        alias: String,
        expr: Box<Expression>,
    },
}

#[derive(Debug, PartialEq)]
pub enum Operator {
    And,
    Or,
    Not,
    Eq,
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    DoubleStar,
    Dot,
    DotDotDot,
    Colon,
    Arrow,
}
