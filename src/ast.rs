#[derive(Debug, PartialEq)]
pub enum Expression {
    Array {
        elements: Vec<Expression>,
    },

    Object(Object),

    // An array postfix coerces the expression into an array.
    // E.g. foo.bar[]
    ArrayTraversal {
        expr: Box<Expression>,
    },

    // A projection operator returns a new object.
    // E.g. *[_type == "person"]{name, "isLegal": age >= 18}
    ProjectionTraversal {
        expr: Box<Expression>,
        object: Object,
    },

    // A filter returns an array filtered another expression.
    // E.g. foo[bar == "baz"], or *[foo == "bar"]
    FilterTraversal {
        expr: Box<Expression>,
        constraint: Box<Expression>,
    },

    SliceTraversal {
        range: Range,
    },

    DereferenceTraversal {
        expr: Box<Expression>,
    },

    AttributeAccess(String),

    ElementAccess {
        expr: Box<Expression>,
        index: Box<Expression>,
    },

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
    start: Box<Expression>,
    end: Box<Expression>,
    inclusive: bool,
}

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
