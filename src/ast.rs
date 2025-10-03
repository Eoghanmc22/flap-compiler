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
pub enum Expr {
    Value(Value),
    Ident(Ident),
    BinaryOp {
        op: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    UnaryOp {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    FunctionCall(FunctionCall),
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
pub struct FunctionCall {
    pub function: Ident,
    pub paramaters: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub function: Ident,
    pub arguements: Vec<(Type, Ident)>,
    pub contents: Block,
    pub return_type: Type,
}

impl FunctionDef {
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
pub struct StaticDef {
    pub name: Ident,
    pub var_type: Type,
    pub value: Value,
}

#[derive(Debug, Clone)]
pub struct LocalDef {
    pub name: Ident,
    pub var_type: Type,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct IfCase {
    pub condition: Expr,
    pub contents: Block,
}

#[derive(Debug, Clone)]
pub struct IfStatement {
    pub cases: Vec<IfCase>,
    pub otherwise: Option<Block>,
}

#[derive(Debug, Clone)]
pub enum Statement {
    FunctionCall(FunctionCall),
    FunctionDef(FunctionDef),
    Static(StaticDef),
    Local(LocalDef),
    Return(Expr),
    If(IfStatement),
}

#[derive(Debug, Clone)]
pub struct Block {
    pub statements: Vec<Statement>,
}
