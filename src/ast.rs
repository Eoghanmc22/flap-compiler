use std::collections::{BTreeMap, HashSet};

use pest::Span;

pub type Ident = String;
pub type IdentRef<'a> = &'a str;

pub trait AsSpan {
    fn as_span(&self) -> Span<'_>;
}

#[derive(Debug, Clone, Copy)]
pub enum Value {
    Int(i32),
    Bool(bool),
}

impl Value {
    pub fn as_repr(&self) -> i32 {
        match self {
            Value::Int(int) => *int,
            Value::Bool(bool) => *bool as _,
        }
    }

    pub fn truthy(&self) -> bool {
        self.as_repr() != 0
    }
}

#[derive(Debug, Clone)]
pub enum Expr<'a> {
    Value(Value, Span<'a>),
    Ident(IdentRef<'a>, Span<'a>),
    BinaryOp {
        op: BinaryOp,
        left: Box<Expr<'a>>,
        right: Box<Expr<'a>>,
        span: Span<'a>,
    },
    UnaryOp {
        op: UnaryOp,
        operand: Box<Expr<'a>>,
        span: Span<'a>,
    },
    FunctionCall(FunctionCall<'a>),
    If(IfExpr<'a>),
}

impl AsSpan for Expr<'_> {
    fn as_span(&self) -> Span<'_> {
        match self {
            Expr::Value(_, span)
            | Expr::Ident(_, span)
            | Expr::BinaryOp { span, .. }
            | Expr::UnaryOp { span, .. }
            | Expr::FunctionCall(FunctionCall { span, .. })
            | Expr::If(IfExpr { span, .. }) => *span,
        }
    }
}

#[derive(Debug, Clone)]
pub enum UnaryOp {
    Negate,
    LNot,
}

#[derive(Debug, Clone)]
pub enum BinaryOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,

    // Comparison
    Eq,
    Ne,
    Le,
    Ge,
    Lt,
    Gt,

    // Logical
    LAnd,
    LOr,

    // Bitwise
    BShl,
    BShr,
    BAnd,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Type {
    Int,
    Bool,
    #[default]
    Void,
}

// TODO: This is a kinda hacky solution
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DeferedType {
    ResolvedType(Type),
    #[default]
    UnresolvedType,
}

impl DeferedType {
    pub fn to_option(&self) -> Option<Type> {
        match *self {
            DeferedType::ResolvedType(var_type) => Some(var_type),
            DeferedType::UnresolvedType => None,
        }
    }

    pub fn unwrap(&self) -> Type {
        self.to_option().unwrap()
    }
}

impl Type {
    pub fn width(&self) -> u32 {
        match self {
            Type::Int | Type::Bool => 1,
            Type::Void => 0,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Captures<'a> {
    pub captures: BTreeMap<IdentRef<'a>, Type>,
}

// TODO: This is a kinda hacky solution
#[derive(Debug, Clone, Default)]
pub enum DeferedCaptures<'a> {
    ResolvedCaptures(Captures<'a>),
    #[default]
    UnresolvedCaptures,
}

impl<'a> DeferedCaptures<'a> {
    pub fn to_option(&self) -> Option<&Captures<'a>> {
        match self {
            DeferedCaptures::ResolvedCaptures(captures) => Some(captures),
            DeferedCaptures::UnresolvedCaptures => None,
        }
    }

    pub fn unwrap(&self) -> &Captures<'a> {
        self.to_option().unwrap()
    }
}

#[derive(Debug, Clone)]
pub struct FunctionCall<'a> {
    pub function: IdentRef<'a>,
    pub parameters: Vec<Expr<'a>>,
    pub span: Span<'a>,
}

impl AsSpan for FunctionCall<'_> {
    fn as_span(&self) -> Span<'_> {
        self.span
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum FunctionAttribute {
    NoMangle,
    AllowUnderflow,
    Naked,
}

#[derive(Debug, Clone)]
pub struct FunctionDef<'a> {
    pub attributes: HashSet<FunctionAttribute>,
    pub function: IdentRef<'a>,
    pub arguements: Vec<(Type, IdentRef<'a>)>,
    pub captures: DeferedCaptures<'a>,
    pub contents: Block<'a>,
    pub return_type: Type,
    pub span: Span<'a>,
}

impl AsSpan for FunctionDef<'_> {
    fn as_span(&self) -> Span<'_> {
        self.span
    }
}

impl FunctionDef<'_> {
    pub fn paramater_width(&self) -> u32 {
        self.arguements
            .iter()
            .map(|(var_type, _)| var_type.width())
            .sum::<u32>()
    }

    pub fn return_width(&self) -> u32 {
        self.return_type.width()
    }

    pub fn stack_delta(&self) -> i32 {
        self.return_width() as i32 - self.paramater_width() as i32
    }
}

#[derive(Debug, Clone)]
pub struct ConstDef<'a> {
    pub name: IdentRef<'a>,
    pub var_type: Type,
    pub value: Value,
    pub span: Span<'a>,
    pub value_span: Span<'a>,
}

impl AsSpan for ConstDef<'_> {
    fn as_span(&self) -> Span<'_> {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct LocalDef<'a> {
    pub name: IdentRef<'a>,
    pub var_type: Type,
    pub expr: Expr<'a>,
    pub span: Span<'a>,
}

impl AsSpan for LocalDef<'_> {
    fn as_span(&self) -> Span<'_> {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct IfCase<'a> {
    pub condition: Expr<'a>,
    pub contents: Block<'a>,
    pub span: Span<'a>,
}

impl AsSpan for IfCase<'_> {
    fn as_span(&self) -> Span<'_> {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct IfExpr<'a> {
    pub cases: Vec<IfCase<'a>>,
    pub otherwise: Option<Block<'a>>,
    pub captures: DeferedCaptures<'a>,
    pub return_type: DeferedType,
    pub span: Span<'a>,
}

impl AsSpan for IfExpr<'_> {
    fn as_span(&self) -> Span<'_> {
        self.span
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Punctuation {
    Punctuated,
    Unpunctuated,
}

#[derive(Debug, Clone)]
pub enum Statement<'a> {
    Expr(Expr<'a>, Punctuation),
    FunctionDef(FunctionDef<'a>),
    Const(ConstDef<'a>),
    Local(LocalDef<'a>),
}

impl AsSpan for Statement<'_> {
    fn as_span(&self) -> Span<'_> {
        match self {
            Statement::Expr(expr, _) => expr.as_span(),
            Statement::FunctionDef(function_def) => function_def.as_span(),
            Statement::Const(const_def) => const_def.as_span(),
            Statement::Local(local_def) => local_def.as_span(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block<'a> {
    pub statements: Vec<Statement<'a>>,
    pub captures: DeferedCaptures<'a>,
    // pub return_type: Type,
    pub span: Span<'a>,
}

impl AsSpan for Block<'_> {
    fn as_span(&self) -> Span<'_> {
        self.span
    }
}
