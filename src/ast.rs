pub type Ident = String;

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

pub enum UnaryOp {
    Negate,
    LNot,
}

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

pub enum Type {
    Int,
    Bool,
}

pub struct FunctionCall {
    pub function: Ident,
    pub paramaters: Vec<Expr>,
}

pub enum Statement {
    FunctionCall(FunctionCall),
    FunctionDef {
        function: Ident,
        arguements: Vec<(Type, Ident)>,
        contents: Block,
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

pub struct Block {
    pub statements: Vec<Statement>,
}

pub struct IfCase {
    pub condition: Expr,
    pub contents: Block,
}
