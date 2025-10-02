pub type Ident = String;

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum Type {
    Int,
    Bool,
}

#[derive(Debug, Clone)]
pub struct FunctionCall {
    pub function: Ident,
    pub paramaters: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub enum Statement {
    FunctionCall(FunctionCall),
    FunctionDef {
        function: Ident,
        arguements: Vec<(Type, Ident)>,
        contents: Block,
        return_type: Type,
    },
    Static {
        name: Ident,
        var_type: Type,
        value: Value,
    },
    Local {
        name: Ident,
        var_type: Type,
        expr: Expr,
    },
    Return {
        value: Expr,
    },
    If {
        cases: Vec<IfCase>,
        otherwise: Option<Block>,
    },
}

#[derive(Debug, Clone)]
pub struct Block {
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub struct IfCase {
    pub condition: Expr,
    pub contents: Block,
}
