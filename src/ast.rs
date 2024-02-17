#[derive(Debug, PartialEq)]
pub struct Expression {
    pub kind: ExpressionKind
    // TODO: Add position information
}

#[derive(Debug, PartialEq)]
pub enum ExpressionKind {
    AttributeAccess(AttributeAccess),
    Dereference(Dereference),
    SliceTraversal(SliceTraversal),
    FilterTraversal(FilterTraversal),
    ElementAccess(ElementAccess),
    ArrayPostfix(ArrayPostfix),
    Projection(Projection),
    ArrayElements(ArrayElements),
    Object(Object),
    BinaryOp(BinaryOp),
    UnaryOp(UnaryOp),
    Literal(LiteralKind),
    Everything,
    Parent,
    Attr(String),
}

// https://sanity-io.github.io/GROQ/GROQ-1.revision1/#AttributeAccess
#[derive(Debug, PartialEq)]
pub struct AttributeAccess {
    pub expr: Box<Expression>,
    pub name: String,
}

// https://sanity-io.github.io/GROQ/GROQ-1.revision1/#Dereference
#[derive(Debug, PartialEq)]
pub struct Dereference {
    pub expr: Box<Expression>,
}

// https://sanity-io.github.io/GROQ/GROQ-1.revision1/#Slice
#[derive(Debug, PartialEq)]
pub struct SliceTraversal {
    pub range: Range,
}


// https://sanity-io.github.io/GROQ/GROQ-1.revision1/#Filter
#[derive(Debug, PartialEq)]
pub struct FilterTraversal {
    pub expr: Box<Expression>,
    pub constraint: Box<Expression>,
}

// https://sanity-io.github.io/GROQ/GROQ-1.revision1/#ElementAccess
#[derive(Debug, PartialEq)]
pub struct ElementAccess {
    pub expr: Box<Expression>,
    pub index: Box<Expression>,
}

// https://sanity-io.github.io/GROQ/GROQ-1.revision1/#ArrayPostfix
#[derive(Debug, PartialEq)]
pub struct ArrayPostfix {
    pub expr: Box<Expression>,
}

// https://sanity-io.github.io/GROQ/GROQ-1.revision1/#Projection
#[derive(Debug, PartialEq)]
pub struct Projection {
    pub expr: Box<Expression>,
    pub object: Object,
}

// https://sanity-io.github.io/GROQ/GROQ-1.revision1/#AttributeAccess
#[derive(Debug, PartialEq)]
pub struct ArrayElements {
    pub elements: Vec<Expression>,
}

#[derive(Debug, PartialEq)]
pub struct BinaryOp {
    pub lhs: Box<Expression>,
    pub operator: Operator,
    pub rhs: Box<Expression>,
}

#[derive(Debug, PartialEq)]
pub struct UnaryOp {
    pub operator: Operator,
    pub expr: Box<Expression>,
}

#[derive(Debug, PartialEq)]
pub struct Literal {
    pub kind: LiteralKind,
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
    DotDot,
    DotDotDot,
    Colon,
    Arrow,
}
