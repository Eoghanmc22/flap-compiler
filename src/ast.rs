use pest::Span;

pub type Ident = String;
pub type IdentRef<'a> = &'a str;

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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Type {
    Int,
    Bool,
    #[default]
    Void,
}

impl Type {
    pub fn width(&self) -> u32 {
        match self {
            Type::Int | Type::Bool => 1,
            Type::Void => 0,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionCall<'a> {
    pub function: IdentRef<'a>,
    pub paramaters: Vec<Expr<'a>>,
    pub span: Span<'a>,
}

#[derive(Debug, Clone)]
pub struct FunctionDef<'a> {
    pub function: IdentRef<'a>,
    pub arguements: Vec<(Type, IdentRef<'a>)>,
    pub contents: Block<'a>,
    pub return_type: Type,
    pub span: Span<'a>,
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
pub struct StaticDef<'a> {
    pub name: IdentRef<'a>,
    pub var_type: Type,
    pub value: Value,
    pub span: Span<'a>,
}

#[derive(Debug, Clone)]
pub struct LocalDef<'a> {
    pub name: IdentRef<'a>,
    pub var_type: Type,
    pub expr: Expr<'a>,
    pub span: Span<'a>,
}

#[derive(Debug, Clone)]
pub struct IfCase<'a> {
    pub condition: Expr<'a>,
    pub contents: Block<'a>,
    pub span: Span<'a>,
}

#[derive(Debug, Clone)]
pub struct IfStatement<'a> {
    pub cases: Vec<IfCase<'a>>,
    pub otherwise: Option<Block<'a>>,
    pub span: Span<'a>,
}

#[derive(Debug, Clone)]
pub enum Statement<'a> {
    FunctionCall(FunctionCall<'a>),
    FunctionDef(FunctionDef<'a>),
    Static(StaticDef<'a>),
    Local(LocalDef<'a>),
    Return(Expr<'a>),
    If(IfStatement<'a>),
}

#[derive(Debug, Clone)]
pub struct Block<'a> {
    pub statements: Vec<Statement<'a>>,
}
