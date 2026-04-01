use crate::{
    codegen::{Offset, clac::ClacValue},
    middleware::generate_span_error_section,
    type_check::TypeChecker,
};
use color_eyre::eyre::{Result, eyre};
use core::fmt;
use pest::Span;
use std::{
    borrow::Cow,
    collections::{BTreeMap, HashSet},
    fmt::{Debug, Display},
    ops::BitOr,
    path::Path,
};

macro_rules! impl_display {
    ($($the_type:ty),*) => {
        $(
            impl Display for $the_type {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
                    write!(f, "\n{}", generate_span_error_section(self.as_span()))
                }
            }
        )*
    };
}

impl_display! {
    Expr<'_>,
    Statement<'_>,
    IfCase<'_>,
    ConstDef<'_>,
    FunctionDef<'_>,
    FunctionCall<'_>,
    IfExpr<'_>,
    Block<'_>,
    LocalDef<'_>,
    Typedef<'_>,
    Assignment<'_>
}

pub type Ident = String;
pub type IdentRef<'a> = &'a str;

pub trait AsSpan<'a> {
    fn as_span(&self) -> Span<'a>;
}

#[derive(Debug, Clone)]
pub enum Value<'a> {
    String(Cow<'a, str>),
    Array(Type<'a>, Vec<Value<'a>>),
    Struct(BTreeMap<IdentRef<'a>, Value<'a>>),
    Int(ClacValue),
    Char(ClacValue),
    Bool(bool),
    Cast(Type<'a>, Box<Value<'a>>),
    Flat(Type<'a>, Vec<ClacValue>),
}

impl<'a> Value<'a> {
    pub fn as_repr(&self) -> Vec<ClacValue> {
        match self {
            Value::Int(int) => vec![*int],
            Value::Char(int) => vec![*int],
            Value::Bool(bool) => vec![*bool as _],
            Value::String(items) => items.bytes().map(|it| it as ClacValue).collect(),
            Value::Array(_, items) => items
                .iter()
                .flat_map(|it| it.as_repr().into_iter())
                .collect(),
            Value::Struct(items) => items
                .values()
                .flat_map(|it| it.as_repr().into_iter())
                .collect(),
            Value::Cast(_, inner) => inner.as_repr(),
            Value::Flat(_, inner) => inner.clone(),
        }
    }

    pub fn truthy(&self) -> bool {
        self.as_repr().into_iter().fold(0, BitOr::bitor) != 0
    }

    pub fn compute_type(&self) -> Type<'a> {
        match self.clone() {
            Value::Int(_) => Type::Int,
            Value::Char(_) => Type::Char,
            Value::Bool(_) => Type::Bool,
            Value::String(items) => Type::Array(Type::Char.into(), items.len() as ClacValue),
            Value::Array(inner_type, items) => {
                Type::Array(inner_type.into(), items.len() as ClacValue)
            }
            Value::Struct(items) => Type::Struct(
                items
                    .iter()
                    .map(|(key, val)| (*key, val.compute_type()))
                    .collect(),
            ),
            Value::Cast(new_type, _) => new_type,
            Value::Flat(inner_type, _) => inner_type,
        }
    }
}

impl<'a> Display for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(int) => <ClacValue as Display>::fmt(int, f),
            Value::Char(char) => <ClacValue as Display>::fmt(char, f),
            Value::Bool(bool) => <bool as Display>::fmt(bool, f),
            Value::String(data) => <Cow<'a, str> as Display>::fmt(data, f),
            Value::Array(_, values) => write!(f, "{values:?}"),
            Value::Struct(values) => write!(f, "{values:?}"),
            Value::Cast(new_type, inner) => write!(f, "({new_type}) {inner}"),
            Value::Flat(inner_type, inner) => write!(f, "({inner_type}) {inner:?}"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum SizeOfMode {
    Native,
    Packed,
}

#[derive(Debug, Clone)]
pub enum Expr<'a> {
    Value(Value<'a>, Span<'a>),
    Variable(IdentRef<'a>, Span<'a>),
    Struct(BTreeMap<IdentRef<'a>, Expr<'a>>, DeferedType<'a>, Span<'a>),
    Array(Vec<Expr<'a>>, DeferedType<'a>, Span<'a>),
    BinaryOp {
        op: BinaryOp,
        left: Box<Expr<'a>>,
        left_type: DeferedType<'a>,
        right: Box<Expr<'a>>,
        right_type: DeferedType<'a>,
        span: Span<'a>,
    },
    PrefixOp {
        op: PrefixOp<'a>,
        operand: Box<Expr<'a>>,
        operand_type: DeferedType<'a>,
        span: Span<'a>,
    },
    PostfixOp {
        op: PostfixOp<'a>,
        operand: Box<Expr<'a>>,
        operand_type: DeferedType<'a>,
        span: Span<'a>,
    },
    FunctionCall(FunctionCall<'a>),
    SizeOfType(Type<'a>, SizeOfMode, Span<'a>),
    SizeOfExpr(Box<Expr<'a>>, DeferedType<'a>, SizeOfMode, Span<'a>),
    If(IfExpr<'a>),
}

impl<'a> AsSpan<'a> for Expr<'a> {
    fn as_span(&self) -> Span<'a> {
        match self {
            Expr::Value(_, span)
            | Expr::Variable(_, span)
            | Expr::Struct(_, _, span)
            | Expr::Array(_, _, span)
            | Expr::BinaryOp { span, .. }
            | Expr::PrefixOp { span, .. }
            | Expr::PostfixOp { span, .. }
            | Expr::FunctionCall(FunctionCall { span, .. })
            | Expr::SizeOfType(_, _, span)
            | Expr::SizeOfExpr(_, _, _, span)
            | Expr::If(IfExpr { span, .. }) => *span,
        }
    }
}

#[derive(Debug, Clone)]
pub enum PrefixOp<'a> {
    Cast(Type<'a>),
    Dereference,
    Negate,
    LNot,
}

impl Display for PrefixOp<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrefixOp::Cast(to) => write!(f, "({to})"),
            PrefixOp::Dereference => write!(f, "*"),
            PrefixOp::Negate => write!(f, "-"),
            PrefixOp::LNot => write!(f, "!"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum PostfixOp<'a> {
    Member(IdentRef<'a>),
    MemberDeref(IdentRef<'a>),
    ArrayIndex(Box<Expr<'a>>),
}

impl Display for PostfixOp<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PostfixOp::Member(field) => write!(f, ".{field}"),
            PostfixOp::MemberDeref(field) => write!(f, ".{field}"),
            PostfixOp::ArrayIndex(idx) => write!(f, "[{idx}]"),
        }
    }
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

impl Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOp::Add => write!(f, "+"),
            BinaryOp::Sub => write!(f, "-"),
            BinaryOp::Mul => write!(f, "*"),
            BinaryOp::Div => write!(f, "/"),
            BinaryOp::Mod => write!(f, "%"),
            BinaryOp::Pow => write!(f, "**"),
            BinaryOp::Eq => write!(f, "=="),
            BinaryOp::Ne => write!(f, "!="),
            BinaryOp::Le => write!(f, "<="),
            BinaryOp::Ge => write!(f, ">="),
            BinaryOp::Lt => write!(f, "<"),
            BinaryOp::Gt => write!(f, ">"),
            BinaryOp::LAnd => write!(f, "&&"),
            BinaryOp::LOr => write!(f, "||"),
            BinaryOp::BShl => write!(f, "<<"),
            BinaryOp::BShr => write!(f, ">>"),
            BinaryOp::BAnd => write!(f, "&"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stride {
    Native,
    Byte,
    ZST,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum Type<'a> {
    Typedef(IdentRef<'a>),
    Struct(BTreeMap<IdentRef<'a>, Type<'a>>),
    Pointer(Box<Type<'a>>),
    Array(Box<Type<'a>>, ClacValue),
    Int,
    Char,
    Bool,
    #[default]
    Void,
}

impl Display for Type<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Typedef(name) => write!(f, "{name}"),
            Type::Struct(map) => write!(f, "struct {map:?}"),
            Type::Pointer(target) => write!(f, "{target}*"),
            Type::Int => write!(f, "int"),
            Type::Char => write!(f, "char"),
            Type::Bool => write!(f, "bool"),
            Type::Void => write!(f, "void"),
            Type::Array(inner_type, len) => write!(f, "[{inner_type}, {len}]"),
        }
    }
}

impl<'a> Type<'a> {
    pub fn resolve(&self, ctx: &TypeChecker<'a>) -> Result<Type<'a>> {
        match self {
            Type::Typedef(ident) => ctx
                .typedefs
                .get(ident)
                .ok_or_else(|| eyre!("No typedef `{ident}` in scope"))
                .and_then(|it| it.resolve(ctx)),
            Type::Struct(btree_map) => Ok(Type::Struct(
                btree_map
                    .into_iter()
                    .map(|(key, val)| Ok((*key, val.resolve(ctx)?)))
                    .collect::<Result<_>>()?,
            )),
            Type::Pointer(ptr) => Ok(Type::Pointer(ptr.resolve(ctx)?.into())),
            Type::Array(inner_type, len) => Ok(Type::Array(inner_type.resolve(ctx)?.into(), *len)),
            Type::Int | Type::Char | Type::Bool | Type::Void => Ok(self.clone()),
        }
    }

    pub fn dereference(&self, ctx: &TypeChecker<'a>) -> Result<Type<'a>> {
        match self {
            Type::Typedef(ident) => ctx
                .typedefs
                .get(ident)
                .ok_or_else(|| eyre!("No typedef `{ident}` in scope"))
                .and_then(|it| it.dereference(ctx)),
            Type::Pointer(target) => Ok((**target).clone()),
            _ => Err(eyre!("Can not dereference type `{self}`")),
        }
    }

    pub fn member(&self, ctx: &TypeChecker<'a>, ident: IdentRef<'a>) -> Result<Type<'a>> {
        match self {
            Type::Typedef(type_def_ident) => ctx
                .typedefs
                .get(type_def_ident)
                .ok_or_else(|| eyre!("No typedef `{ident}` in scope"))
                .and_then(|it| it.member(ctx, ident)),
            Type::Struct(map) => map
                .get(ident)
                .ok_or_else(|| eyre!("Type `{self}` has no member with name {ident}"))
                .cloned(),
            _ => Err(eyre!("Type `{self}` has no members")),
        }
    }

    pub fn member_and_offset(
        &self,
        ctx: &TypeChecker<'a>,
        ident: IdentRef<'a>,
    ) -> Result<(Type<'a>, Offset)> {
        match self {
            Type::Typedef(type_def_ident) => ctx
                .typedefs
                .get(type_def_ident)
                .ok_or_else(|| eyre!("No typedef `{ident}` in scope"))
                .and_then(|it| it.member_and_offset(ctx, ident)),
            Type::Struct(map) => {
                let mut offset = 0;

                for (field_name, field_type) in map {
                    if *field_name == ident {
                        return Ok((field_type.clone(), Offset(offset)));
                    }

                    offset += field_type.width(ctx)?;
                }

                Err(eyre!("Type `{self}` has no member with name {ident}"))
            }
            _ => Err(eyre!("Type `{self}` has no members")),
        }
    }

    pub fn width(&self, ctx: &TypeChecker<'a>) -> Result<ClacValue> {
        match self {
            Type::Typedef(ident) => ctx
                .typedefs
                .get(ident)
                .ok_or_else(|| eyre!("No typedef `{ident}` in scope"))
                .and_then(|it| it.width(ctx)),
            Type::Struct(map) => map
                .values()
                .map(|it| it.width(ctx))
                .sum::<Result<ClacValue>>(),
            Type::Pointer(_) | Type::Int | Type::Char | Type::Bool => Ok(1),
            Type::Void => Ok(0),
            Type::Array(inner_type, len) => Ok(inner_type.width(ctx)? * *len),
        }
    }

    pub fn stride(&self, ctx: &TypeChecker<'a>) -> Result<Stride> {
        match self {
            Type::Typedef(ident) => ctx
                .typedefs
                .get(ident)
                .ok_or_else(|| eyre!("No typedef `{ident}` in scope"))
                .and_then(|it| it.stride(ctx)),
            Type::Char => Ok(Stride::Byte),
            Type::Void => Ok(Stride::ZST),
            // Type::Array(inner_type, _len) => inner_type.stride(ctx),
            _ => Ok(Stride::Native),
        }
    }

    pub fn is_canonical(&self, ctx: &TypeChecker<'a>) -> Result<bool> {
        Ok(&self.resolve(ctx)? == self)
    }
}

// TODO: This is a kinda hacky solution
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum DeferedType<'a> {
    ResolvedType(Type<'a>),
    #[default]
    UnresolvedType,
}

impl Display for DeferedType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DeferedType::ResolvedType(t) => <Type as Display>::fmt(t, f),
            DeferedType::UnresolvedType => write!(f, "unresolved"),
        }
    }
}

impl<'a> DeferedType<'a> {
    pub fn to_option(self) -> Option<Type<'a>> {
        match self {
            DeferedType::ResolvedType(var_type) => Some(var_type),
            DeferedType::UnresolvedType => None,
        }
    }

    pub fn unwrap(self) -> Type<'a> {
        self.to_option().unwrap()
    }
}

#[derive(Debug, Clone, Default)]
pub struct Captures<'a> {
    pub captures: BTreeMap<IdentRef<'a>, Type<'a>>,
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

impl<'a> AsSpan<'a> for FunctionCall<'a> {
    fn as_span(&self) -> Span<'a> {
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
    pub captures: DeferedCaptures<'a>,
    pub contents: Block<'a>,
    pub span: Span<'a>,
    pub signature: FunctionSignature<'a>,
}

impl<'a> AsSpan<'a> for FunctionDef<'a> {
    fn as_span(&self) -> Span<'a> {
        self.span
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FunctionSignature<'a> {
    pub arguements: Vec<(Type<'a>, IdentRef<'a>)>,
    pub return_type: Type<'a>,
}

impl<'a> FunctionSignature<'a> {
    pub fn paramater_width(&self, ctx: &TypeChecker<'a>) -> Result<ClacValue> {
        self.arguements
            .iter()
            .map(|(var_type, _)| var_type.width(ctx))
            .sum::<Result<ClacValue>>()
    }

    pub fn return_width(&self, ctx: &TypeChecker<'a>) -> Result<ClacValue> {
        self.return_type.width(ctx)
    }

    pub fn stack_delta(&self, ctx: &TypeChecker<'a>) -> Result<ClacValue> {
        self.return_width(ctx).and_then(|ret_width| {
            self.paramater_width(ctx)
                .map(|parm_width| ret_width - parm_width)
        })
    }
}

#[derive(Debug, Clone)]
pub struct ConstDef<'a> {
    pub name: IdentRef<'a>,
    pub var_type: DeferedType<'a>,
    pub expr: Expr<'a>,
    pub span: Span<'a>,
    pub expr_span: Span<'a>,
}

impl<'a> AsSpan<'a> for ConstDef<'a> {
    fn as_span(&self) -> Span<'a> {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct IfCase<'a> {
    pub condition: Expr<'a>,
    pub contents: Block<'a>,
    pub span: Span<'a>,
}

impl<'a> AsSpan<'a> for IfCase<'a> {
    fn as_span(&self) -> Span<'a> {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct LocalDef<'a> {
    pub name: IdentRef<'a>,
    pub var_type: DeferedType<'a>,
    pub expr: Expr<'a>,
    pub span: Span<'a>,
    pub expr_span: Span<'a>,
}

impl<'a> AsSpan<'a> for LocalDef<'a> {
    fn as_span(&self) -> Span<'a> {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct Assignment<'a> {
    pub target: Expr<'a>,
    pub expr: Expr<'a>,
    pub span: Span<'a>,
    pub expr_span: Span<'a>,
    pub target_type: DeferedType<'a>,
    pub expr_type: DeferedType<'a>,
}

impl<'a> AsSpan<'a> for Assignment<'a> {
    fn as_span(&self) -> Span<'a> {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct Typedef<'a> {
    pub type_alias: Type<'a>,
    pub name: IdentRef<'a>,
    pub span: Span<'a>,
}

impl<'a> AsSpan<'a> for Typedef<'a> {
    fn as_span(&self) -> Span<'a> {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct IfExpr<'a> {
    pub cases: Vec<IfCase<'a>>,
    pub otherwise: Option<Block<'a>>,
    pub captures: DeferedCaptures<'a>,
    pub return_type: DeferedType<'a>,
    pub span: Span<'a>,
}

impl<'a> AsSpan<'a> for IfExpr<'a> {
    fn as_span(&self) -> Span<'a> {
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
    Assignment(Assignment<'a>),
    Typedef(Typedef<'a>),
}

impl<'a> AsSpan<'a> for Statement<'a> {
    fn as_span(&self) -> Span<'a> {
        match self {
            Statement::Expr(expr, _) => expr.as_span(),
            Statement::FunctionDef(function_def) => function_def.as_span(),
            Statement::Const(const_def) => const_def.as_span(),
            Statement::Local(local_def) => local_def.as_span(),
            Statement::Assignment(ptr_assign) => ptr_assign.as_span(),
            Statement::Typedef(typedef) => typedef.as_span(),
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

impl<'a> AsSpan<'a> for Block<'a> {
    fn as_span(&self) -> Span<'a> {
        self.span
    }
}

#[derive(Debug, Clone)]
pub struct Program<'a> {
    pub directives: Vec<Directive<'a>>,
    pub code: Block<'a>,
}

impl<'a> AsSpan<'a> for Program<'a> {
    fn as_span(&self) -> Span<'a> {
        self.code.span
    }
}

#[derive(Debug, Clone)]
pub enum Directive<'a> {
    Include(&'a Path),
}
