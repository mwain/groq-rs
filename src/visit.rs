use crate::ast::*;
use core::ops::ControlFlow;

pub trait Visitor {
    type Break;

    fn visit_expression(&mut self, expr: &Expression) -> ControlFlow<Self::Break>;
}

pub fn walk_expression<V: Visitor>(visitor: &mut V, expr: &Expression) -> ControlFlow<V::Break> {
    visitor.visit_expression(expr)?;

    match &expr.kind {
        ExpressionKind::AttributeAccess(attr) => {
            walk_expression(visitor, &attr.expr)?;
        }
        ExpressionKind::Dereference(deref) => {
            walk_expression(visitor, &deref.expr)?;
        }
        ExpressionKind::SliceTraversal(slice) => {
            walk_expression(visitor, &slice.range.start)?;
            walk_expression(visitor, &slice.range.end)?;
        }
        ExpressionKind::FilterTraversal(filter) => {
            walk_expression(visitor, &filter.expr)?;
            walk_expression(visitor, &filter.constraint)?;
        }
        ExpressionKind::ElementAccess(access) => {
            walk_expression(visitor, &access.expr)?;
            walk_expression(visitor, &access.index)?;
        }
        ExpressionKind::ArrayPostfix(array) => {
            walk_expression(visitor, &array.expr)?;
        }
        ExpressionKind::Projection(proj) => {
            walk_expression(visitor, &proj.expr)?;
            for attr in &proj.object.entries {
                match attr {
                    ObjectAttribute::Expression(expr)
                    | ObjectAttribute::AliasedExpression { expr, .. } => {
                        walk_expression(visitor, expr)?;
                    }
                }
            }
        }
        ExpressionKind::ArrayElements(array) => {
            for elem in &array.elements {
                walk_expression(visitor, elem)?;
            }
        }
        ExpressionKind::Object(obj) => {
            for attr in &obj.entries {
                match attr {
                    ObjectAttribute::Expression(expr)
                    | ObjectAttribute::AliasedExpression { expr, .. } => {
                        walk_expression(visitor, expr)?;
                    }
                }
            }
        }
        ExpressionKind::BinaryOp(binary) => {
            walk_expression(visitor, &binary.lhs)?;
            walk_expression(visitor, &binary.rhs)?;
        }
        ExpressionKind::UnaryOp(unary) => {
            walk_expression(visitor, &unary.expr)?;
        }
        ExpressionKind::Literal(_) | ExpressionKind::Everything | ExpressionKind::Attr(_) => {}
    }

    ControlFlow::Continue(())
}

pub struct ClosureVisitor<F, T>
where
    F: FnMut(&Expression) -> ControlFlow<T>,
{
    f: F,
}

impl <F, T> ClosureVisitor<F, T>
where
    F: FnMut(&Expression) -> ControlFlow<T>,
{
    pub fn walk(expr: &Expression, f: F) -> ControlFlow<T> {
        let mut visitor = Self { f };
        walk_expression(&mut visitor, expr)
    }
}

impl <F, T> Visitor for ClosureVisitor<F, T>
where
    F: FnMut(&Expression) -> ControlFlow<T>,
{
    type Break = T;

    fn visit_expression(&mut self, expr: &Expression) -> ControlFlow<T> {
        (self.f)(expr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    struct TestVisitor {
        visited: Vec<String>,
    }

    impl Visitor for TestVisitor {
        type Break = ();

        fn visit_expression(&mut self, expr: &Expression) -> ControlFlow<()> {
            match &expr.kind {
                ExpressionKind::AttributeAccess(_) => {
                    self.visited.push("AttributeAccess".to_string());
                }
                ExpressionKind::Dereference(_) => {
                    self.visited.push("Dereference".to_string());
                }
                ExpressionKind::SliceTraversal(_) => {
                    self.visited.push("SliceTraversal".to_string());
                }
                ExpressionKind::FilterTraversal(_) => {
                    self.visited.push("FilterTraversal".to_string());
                }
                ExpressionKind::ElementAccess(_) => {
                    self.visited.push("ElementAccess".to_string());
                }
                ExpressionKind::ArrayPostfix(_) => {
                    self.visited.push("ArrayPostfix".to_string());
                }
                ExpressionKind::Projection(_) => {
                    self.visited.push("Projection".to_string());
                }
                ExpressionKind::ArrayElements(_) => {
                    self.visited.push("ArrayElements".to_string());
                }
                ExpressionKind::Object(_) => {
                    self.visited.push("Object".to_string());
                }
                ExpressionKind::BinaryOp(_) => {
                    self.visited.push("BinaryOp".to_string());
                }
                ExpressionKind::UnaryOp(_) => {
                    self.visited.push("UnaryOp".to_string());
                }
                ExpressionKind::Literal(_) => {
                    self.visited.push("Literal".to_string());
                }
                ExpressionKind::Everything => {
                    self.visited.push("Everything".to_string());
                }
                ExpressionKind::Attr(_) => {
                    self.visited.push("Attr".to_string());
                }
            }

            ControlFlow::Continue(())
        }
    }

    #[test]
    fn test_visitor() {
        // TODO: add more tests
        let query = r#"
            foo[].bar[]
        "#;
        let lex: Lexer<'_> = Lexer::new(query);
        let mut parser = Parser::new(lex);
        let expr = parser.parse().unwrap();

        let mut visitor = TestVisitor { visited: vec![] };
        walk_expression(&mut visitor, &expr);
        assert_eq!(visitor.visited, vec![
            "ArrayPostfix",
            "AttributeAccess",
            "ArrayPostfix",
            "Attr",
        ]);
    }

    #[test]
    fn test_closure() {
        let query = r#"
            foo[].bar[] {
                baz
            }
        "#;
        let lex: Lexer<'_> = Lexer::new(query);
        let mut parser = Parser::new(lex);
        let expr = parser.parse().unwrap();

        let res = ClosureVisitor::walk(&expr, |expr| {
            match &expr.kind {
                ExpressionKind::Projection(_) => {
                    ControlFlow::Break(())
                }
                _ => ControlFlow::Continue(())
            }
        });
        assert_eq!(res, ControlFlow::Break(()));
    }
}
