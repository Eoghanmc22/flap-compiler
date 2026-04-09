use crate::{
    codegen::{Offset, clac::ClacValue},
    middleware::generate_span_error_section,
    type_check::TypeChecker,
};
use color_eyre::eyre::{Result, eyre};
use pest::Span;
use std::{
    borrow::Cow,
    collections::{BTreeMap, HashSet},
    fmt::{self, Debug, Display},
    iter,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AnnotatedSpan<'a> {
    pub span: Span<'a>,
    pub file_name: &'a str,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OwnedSpan {
    pub start: (usize, usize),
    pub end: (usize, usize),
    pub content: String,
    pub file_name: String,
}

impl OwnedSpan {
    pub fn new(content: impl Into<String>, file_name: impl Into<String>) -> Self {
        let content = content.into();
        let file_name = file_name.into();
        Self {
            start: (1, 1),
            end: (1, content.len() + 1),
            content,
            file_name,
        }
    }
}

impl From<AnnotatedSpan<'_>> for OwnedSpan {
    fn from(value: AnnotatedSpan) -> Self {
        let (start, end) = value.span.split();

        Self {
            start: start.line_col(),
            end: end.line_col(),
            content: value.span.as_str().to_owned(),
            file_name: value.file_name.to_owned(),
        }
    }
}

pub trait AstSpan<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a>;
    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_>;
    fn as_ast_node(&self) -> AstNode<'a, '_>;
}

pub fn nearest_node<'a, 'b>(
    node: &'b dyn AstSpan<'a>,
    line: usize,
    column: usize,
) -> &'b dyn AstSpan<'a> {
    let goal = (line, column);

    for child in node.children() {
        let span = child.as_span();
        let start = span.span.start_pos().line_col();
        let end = span.span.end_pos().line_col();

        if start <= goal && goal < end {
            return nearest_node(child, line, column);
        }
    }

    node
}

#[derive(Debug, Clone)]
pub enum AstNode<'a, 'b> {
    Expr(&'b Expr<'a>),
    FunctionCall(&'b FunctionCall<'a>),
    FunctionDef(&'b FunctionDef<'a>),
    ConstDef(&'b ConstDef<'a>),
    IfCase(&'b IfCase<'a>),
    LocalDef(&'b LocalDef<'a>),
    Assignment(&'b Assignment<'a>),
    Typedef(&'b Typedef<'a>),
    IfExpr(&'b IfExpr<'a>),
    Loop(&'b Loop<'a>),
    Statement(&'b Statement<'a>),
    Block(&'b Block<'a>),
    Program(&'b Program<'a>),
    Directive(&'b Directive<'a>),
}

impl<'a, 'b, T: AstSpan<'a>> From<&'b T> for AstNode<'a, 'b> {
    fn from(value: &'b T) -> Self {
        value.as_ast_node()
    }
}

#[derive(Debug, Clone)]
pub enum Value<'a> {
    String(Cow<'a, str>),
    Array(Type<'a>, Vec<Value<'a>>),
    Struct(BTreeMap<IdentRef<'a>, Value<'a>>),
    NamedTuple(Vec<(IdentRef<'a>, Value<'a>)>),
    Tuple(Vec<Value<'a>>),
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
            Value::NamedTuple(items) => items
                .iter()
                .flat_map(|(_, it)| it.as_repr().into_iter())
                .collect(),
            Value::Tuple(items) => items
                .iter()
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
            Value::NamedTuple(items) => Type::NamedTuple(
                items
                    .iter()
                    .map(|(key, val)| (*key, val.compute_type()))
                    .collect(),
            ),
            Value::Tuple(items) => Type::Tuple(items.iter().map(|it| it.compute_type()).collect()),
            Value::Cast(new_type, _) => new_type,
            Value::Flat(inner_type, _) => inner_type,
        }
    }
}

impl<'a> Display for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(int) => <ClacValue as Display>::fmt(int, f),
            Value::Char(char) => <ClacValue as Display>::fmt(char, f),
            Value::Bool(bool) => <bool as Display>::fmt(bool, f),
            Value::String(data) => <Cow<'a, str> as Display>::fmt(data, f),
            Value::Array(_, values) => write!(f, "{values:?}"),
            Value::Struct(values) => write!(f, "{values:?}"),
            Value::NamedTuple(values) => write!(f, "{values:?}"),
            Value::Tuple(values) => write!(f, "{values:?}"),
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
    Value(Value<'a>, AnnotatedSpan<'a>),
    Variable(IdentRef<'a>, DeferedVersion, AnnotatedSpan<'a>),
    Struct(
        BTreeMap<IdentRef<'a>, Expr<'a>>,
        DeferedType<'a>,
        AnnotatedSpan<'a>,
    ),
    Array(Vec<Expr<'a>>, DeferedType<'a>, AnnotatedSpan<'a>),
    BinaryOp {
        op: BinaryOp,
        left: Box<Expr<'a>>,
        left_type: DeferedType<'a>,
        right: Box<Expr<'a>>,
        right_type: DeferedType<'a>,
        span: AnnotatedSpan<'a>,
        op_span: AnnotatedSpan<'a>,
    },
    PrefixOp {
        op: PrefixOp<'a>,
        operand: Box<Expr<'a>>,
        operand_type: DeferedType<'a>,
        span: AnnotatedSpan<'a>,
        op_span: AnnotatedSpan<'a>,
    },
    PostfixOp {
        op: PostfixOp<'a>,
        operand: Box<Expr<'a>>,
        operand_type: DeferedType<'a>,
        span: AnnotatedSpan<'a>,
        op_span: AnnotatedSpan<'a>,
    },
    FunctionCall(FunctionCall<'a>),
    SizeOfType(Type<'a>, SizeOfMode, AnnotatedSpan<'a>),
    SizeOfExpr(
        Box<Expr<'a>>,
        DeferedType<'a>,
        SizeOfMode,
        AnnotatedSpan<'a>,
    ),
    If(IfExpr<'a>),
}

impl<'a> AstSpan<'a> for Expr<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        match self {
            Expr::Value(_, span)
            | Expr::Variable(_, _, span)
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

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::from_coroutine(
            #[coroutine]
            || match self {
                Expr::Value(..) => {}
                Expr::Variable(..) => {}
                Expr::Struct(map, ..) => {
                    for expr in map.values() {
                        yield expr as &dyn AstSpan<'a>;
                    }
                }
                Expr::Array(exprs, ..) => {
                    for expr in exprs {
                        yield expr;
                    }
                }
                Expr::BinaryOp { left, right, .. } => {
                    yield &**left;
                    yield &**right;
                }
                Expr::PrefixOp { operand, .. } => {
                    yield &**operand;
                }
                Expr::PostfixOp { operand, op, .. } => {
                    yield &**operand;

                    match op {
                        PostfixOp::ArrayIndex(expr) => yield &**expr,
                        _ => {}
                    }
                }
                Expr::FunctionCall(function_call) => {
                    yield function_call;
                }
                Expr::SizeOfType(..) => {}
                Expr::SizeOfExpr(expr, ..) => {
                    yield &**expr;
                }
                Expr::If(if_expr) => {
                    yield if_expr;
                }
            },
        ))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::Expr(self)
    }
}

#[derive(Debug, Clone)]
pub enum PrefixOp<'a> {
    Cast(Type<'a>),
    Dereference,
    AddressOf,
    Negate,
    LNot,
}

impl Display for PrefixOp<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrefixOp::Cast(to) => write!(f, "({to})"),
            PrefixOp::Dereference => write!(f, "*"),
            PrefixOp::AddressOf => write!(f, "&"),
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PostfixOp::Member(field) => write!(f, ".{field}"),
            PostfixOp::MemberDeref(field) => write!(f, "->{field}"),
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

#[derive(Debug, Clone, Default)]
pub enum Type<'a> {
    Typedef(IdentRef<'a>),
    Struct(BTreeMap<IdentRef<'a>, Type<'a>>),
    NamedTuple(Vec<(IdentRef<'a>, Type<'a>)>),
    Tuple(Vec<Type<'a>>),
    Pointer(Box<Type<'a>>),
    Array(Box<Type<'a>>, ClacValue),
    Int,
    Char,
    Bool,
    #[default]
    Void,
}

impl Display for Type<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Typedef(name) => write!(f, "{name}"),
            Type::Struct(map) => write!(f, "struct {map:?}"),
            Type::NamedTuple(items) => write!(f, "tuple_struct {items:?}"),
            Type::Tuple(items) => write!(f, "tuple {items:?}"),
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
    pub fn compatible_with(&self, other: &Type<'a>, ctx: &TypeChecker<'a>) -> Result<bool> {
        let lhs = self;
        let rhs = other;

        if let (Type::Typedef(lhs), Type::Typedef(rhs)) = (lhs, rhs) {
            if lhs == rhs {
                return Ok(true);
            }
        }

        let lhs = self.resolve_once(ctx)?;
        let rhs = other.resolve_once(ctx)?;

        match (lhs, rhs) {
            (Type::Struct(lhs_map), Type::Struct(rhs_map)) => {
                for (lhs_key, lhs_value) in &lhs_map {
                    let Some(rhs_value) = rhs_map.get(lhs_key) else {
                        return Ok(false);
                    };

                    if !lhs_value.compatible_with(rhs_value, ctx)? {
                        return Ok(false);
                    }
                }
                for (rhs_key, rhs_value) in &rhs_map {
                    let Some(lhs_value) = lhs_map.get(rhs_key) else {
                        return Ok(false);
                    };

                    if !rhs_value.compatible_with(lhs_value, ctx)? {
                        return Ok(false);
                    }
                }

                Ok(true)
            }
            (Type::NamedTuple(lhs_items), Type::NamedTuple(rhs_items)) => {
                if lhs_items.len() != rhs_items.len() {
                    return Ok(false);
                }

                for ((lhs_key, lhs_value), (rhs_key, rhs_value)) in lhs_items.iter().zip(&rhs_items)
                {
                    if lhs_key != rhs_key {
                        return Ok(false);
                    }

                    if !lhs_value.compatible_with(rhs_value, ctx)? {
                        return Ok(false);
                    }
                }

                Ok(true)
            }
            (Type::Tuple(lhs_items), Type::Tuple(rhs_items)) => {
                if lhs_items.len() != rhs_items.len() {
                    return Ok(false);
                }

                for (lhs_value, rhs_value) in lhs_items.iter().zip(&rhs_items) {
                    if !lhs_value.compatible_with(rhs_value, ctx)? {
                        return Ok(false);
                    }
                }

                Ok(true)
            }
            (Type::Pointer(lhs_inner), Type::Pointer(rhs_inner)) => {
                if matches!(&*lhs_inner, Type::Void) || matches!(&*rhs_inner, Type::Void) {
                    return Ok(true);
                }

                Ok(lhs_inner.compatible_with(&*rhs_inner, ctx)?)
            }
            (Type::Array(lhs_inner, lhs_len), Type::Array(rhs_inner, rhs_len)) => {
                Ok(lhs_inner.compatible_with(&rhs_inner, ctx)? && lhs_len == rhs_len)
            }
            (Type::Int, Type::Int) => Ok(true),
            (Type::Char, Type::Char) => Ok(true),
            (Type::Bool, Type::Bool) => Ok(true),
            (Type::Void, Type::Void) => Ok(true),
            _ => Ok(false),
        }
    }

    pub fn resolve_once(&self, ctx: &TypeChecker<'a>) -> Result<Type<'a>> {
        match self {
            Type::Typedef(ident) => ctx
                .typedefs
                .get(ident)
                .ok_or_else(|| eyre!("No typedef `{ident}` in scope"))
                .and_then(|it| it.resolve_once(ctx)),
            _ => Ok(self.clone()),
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
            Type::NamedTuple(items) => items
                .iter()
                .find(|(name, _)| *name == ident)
                .map(|(_, field_type)| field_type)
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
            Type::NamedTuple(items) => {
                let mut offset = 0;

                for (field_name, field_type) in items {
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
            Type::NamedTuple(items) => items
                .iter()
                .map(|(_name, field_type)| field_type.width(ctx))
                .sum::<Result<ClacValue>>(),
            Type::Tuple(items) => items
                .iter()
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
}

// TODO: This is a kinda hacky solution
#[derive(Debug, Clone, Default)]
pub enum DeferedType<'a> {
    ResolvedType(Type<'a>),
    #[default]
    UnresolvedType,
}

impl Display for DeferedType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeferedType::ResolvedType(t) => <Type as Display>::fmt(t, f),
            DeferedType::UnresolvedType => write!(f, "unresolved"),
        }
    }
}

impl<'a> DeferedType<'a> {
    pub fn compatible_with(&self, other: &Type<'a>, ctx: &TypeChecker<'a>) -> Result<bool> {
        match self {
            DeferedType::ResolvedType(inner) => inner.compatible_with(other, ctx),
            DeferedType::UnresolvedType => Err(eyre!(
                "COMPILER BUG: compatible_with called on unresolved defered type"
            )),
        }
    }

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VariableVersion(pub u64);

impl Display for VariableVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}
#[derive(Debug, Clone, Copy, Default)]
pub enum DeferedVersion {
    ResolvedVersion(VariableVersion),
    #[default]
    UnresolvedVersion,
}

impl DeferedVersion {
    pub fn to_option(&self) -> Option<VariableVersion> {
        match self {
            DeferedVersion::ResolvedVersion(variable_version) => Some(*variable_version),
            DeferedVersion::UnresolvedVersion => None,
        }
    }

    pub fn unwrap(&self) -> VariableVersion {
        self.to_option().unwrap()
    }
}

// TODO: need a way to repersent scopes where captures are not taken such as arguements to
// sizeof() expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CaptureKind {
    Read,
    ReadWrite,
}

pub type Capture<'a> = (Type<'a>, IdentRef<'a>, VariableVersion, CaptureKind);

#[derive(Debug, Clone, Default)]
pub struct Captures<'a>(pub BTreeMap<VariableVersion, (Type<'a>, IdentRef<'a>, CaptureKind)>);

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
    pub span: AnnotatedSpan<'a>,
}

impl<'a> AstSpan<'a> for FunctionCall<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        self.span
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::from_coroutine(
            #[coroutine]
            || {
                for expr in &self.parameters {
                    yield expr as &dyn AstSpan<'a>;
                }
            },
        ))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::FunctionCall(self)
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
    pub contents: Block<'a>,
    pub span: AnnotatedSpan<'a>,
    pub signature: FunctionSignature<'a>,
}

impl<'a> AstSpan<'a> for FunctionDef<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        self.span
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::once(&self.contents as &dyn AstSpan<'a>))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::FunctionDef(self)
    }
}

pub type Arguement<'a> = (Type<'a>, IdentRef<'a>, DeferedVersion);
pub type Arguements<'a> = Vec<Arguement<'a>>;

#[derive(Debug, Clone, Default)]
pub struct FunctionSignature<'a> {
    pub arguements: Arguements<'a>,
    pub captures: DeferedCaptures<'a>,
    pub return_type: Type<'a>,
}

impl<'a> FunctionSignature<'a> {
    pub fn captures_read(&self) -> Result<impl Iterator<Item = Capture<'a>>> {
        let DeferedCaptures::ResolvedCaptures(captures) = &self.captures else {
            return Err(eyre!("COMPILER BUG: defered captures was not resolved"));
        };

        Ok(captures
            .0
            .iter()
            .map(|(version, (var_type, ident, kind))| (var_type.clone(), *ident, *version, *kind)))
    }

    pub fn captures_write(&self) -> Result<impl Iterator<Item = Capture<'a>>> {
        let DeferedCaptures::ResolvedCaptures(captures) = &self.captures else {
            return Err(eyre!("COMPILER BUG: defered captures was not resolved"));
        };

        Ok(captures
            .0
            .iter()
            .filter(|(_, (_, _, kind))| matches!(kind, CaptureKind::ReadWrite))
            .map(|(version, (var_type, ident, kind))| (var_type.clone(), *ident, *version, *kind)))
    }

    pub fn arguements_and_captures(&self) -> Result<impl Iterator<Item = Arguement<'a>>> {
        Ok(self
            .captures_read()?
            .map(|(var_type, ident, version, _kind)| {
                (var_type, ident, DeferedVersion::ResolvedVersion(version))
            })
            .chain(
                self.arguements
                    .iter()
                    .map(|(var_type, ident, version)| (var_type.clone(), *ident, *version)),
            ))
    }

    pub fn full_return_type(&self) -> Result<Type<'a>> {
        Ok(Type::Tuple(
            self.captures_write()?
                .map(|(var_type, _, _, _)| var_type)
                .chain(iter::once(self.return_type.clone()))
                .collect(),
        ))
    }

    pub fn paramater_width(&self, ctx: &TypeChecker<'a>) -> Result<ClacValue> {
        self.arguements_and_captures()?
            .map(|(var_type, _, _)| var_type.width(ctx))
            .sum::<Result<ClacValue>>()
    }

    pub fn return_width(&self, ctx: &TypeChecker<'a>) -> Result<ClacValue> {
        self.full_return_type()?.width(ctx)
    }

    pub fn stack_delta(&self, ctx: &TypeChecker<'a>) -> Result<ClacValue> {
        self.return_width(ctx).and_then(|ret_width| {
            self.paramater_width(ctx)
                .map(|parm_width| ret_width - parm_width)
        })
    }

    pub fn compatible_captures_read(&self, other: &FunctionSignature<'a>) -> Result<bool> {
        let lhs_count = self.captures_read()?.count();
        let rhs_count = other.captures_read()?.count();

        if lhs_count != rhs_count {
            return Ok(false);
        }

        for ((_, _, l_version, _), (_, _, r_version, _)) in
            self.captures_read()?.zip(other.captures_read()?)
        {
            if l_version != r_version {
                return Ok(false);
            }
        }

        Ok(true)
    }

    pub fn compatible_captures_write(&self, other: &FunctionSignature<'a>) -> Result<bool> {
        let lhs_count = self.captures_write()?.count();
        let rhs_count = other.captures_write()?.count();

        if lhs_count != rhs_count {
            return Ok(false);
        }

        for ((_, _, l_version, _), (_, _, r_version, _)) in
            self.captures_write()?.zip(other.captures_write()?)
        {
            if l_version != r_version {
                return Ok(false);
            }
        }

        Ok(true)
    }
}

#[derive(Debug, Clone)]
pub struct ConstDef<'a> {
    pub name: IdentRef<'a>,
    pub var_type: DeferedType<'a>,
    pub version: DeferedVersion,
    pub expr: Expr<'a>,
    pub span: AnnotatedSpan<'a>,
    pub expr_span: AnnotatedSpan<'a>,
}

impl<'a> AstSpan<'a> for ConstDef<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        self.span
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::from_coroutine(
            #[coroutine]
            || {
                yield &self.expr as &dyn AstSpan<'a>;
            },
        ))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::ConstDef(self)
    }
}

#[derive(Debug, Clone)]
pub struct IfCase<'a> {
    pub condition: Expr<'a>,
    pub contents: Block<'a>,
    pub span: AnnotatedSpan<'a>,
}

impl<'a> AstSpan<'a> for IfCase<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        self.span
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::from_coroutine(
            #[coroutine]
            || {
                yield &self.condition as &dyn AstSpan<'a>;
                yield &self.contents;
            },
        ))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::IfCase(self)
    }
}

#[derive(Debug, Clone)]
pub struct LocalDef<'a> {
    pub name: IdentRef<'a>,
    pub var_type: DeferedType<'a>,
    pub version: DeferedVersion,
    pub expr: Expr<'a>,
    pub span: AnnotatedSpan<'a>,
    pub expr_span: AnnotatedSpan<'a>,
}

impl<'a> AstSpan<'a> for LocalDef<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        self.span
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::from_coroutine(
            #[coroutine]
            || {
                yield &self.expr as &dyn AstSpan<'a>;
            },
        ))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::LocalDef(self)
    }
}

#[derive(Debug, Clone)]
pub struct Assignment<'a> {
    pub target: Expr<'a>,
    pub expr: Expr<'a>,
    pub span: AnnotatedSpan<'a>,
    pub expr_span: AnnotatedSpan<'a>,
    pub target_type: DeferedType<'a>,
    pub expr_type: DeferedType<'a>,
}

impl<'a> AstSpan<'a> for Assignment<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        self.span
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::from_coroutine(
            #[coroutine]
            || {
                yield &self.target as &dyn AstSpan<'a>;
                yield &self.expr;
            },
        ))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::Assignment(self)
    }
}

#[derive(Debug, Clone)]
pub struct Typedef<'a> {
    pub type_alias: Type<'a>,
    pub name: IdentRef<'a>,
    pub span: AnnotatedSpan<'a>,
}

impl<'a> AstSpan<'a> for Typedef<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        self.span
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::empty())
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::Typedef(self)
    }
}

#[derive(Debug, Clone)]
pub struct IfExpr<'a> {
    pub cases: Vec<IfCase<'a>>,
    pub otherwise: Option<Block<'a>>,
    pub captures: DeferedCaptures<'a>,
    pub return_type: DeferedType<'a>,
    pub span: AnnotatedSpan<'a>,
}

impl<'a> AstSpan<'a> for IfExpr<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        self.span
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::from_coroutine(
            #[coroutine]
            || {
                for case in &self.cases {
                    yield case as &dyn AstSpan<'a>;
                }
                if let Some(otherwise) = &self.otherwise {
                    yield otherwise;
                }
            },
        ))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::IfExpr(self)
    }
}

#[derive(Debug, Clone)]
pub struct Loop<'a> {
    pub init: Option<LocalDef<'a>>,
    pub cond: Option<Expr<'a>>,
    pub update: Option<Assignment<'a>>,
    pub captures: DeferedCaptures<'a>,
    pub body: Block<'a>,
    pub span: AnnotatedSpan<'a>,
}

impl<'a> AstSpan<'a> for Loop<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        self.span
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::from_coroutine(
            #[coroutine]
            || {
                if let Some(init) = &self.init {
                    yield init as &dyn AstSpan<'a>;
                }

                if let Some(cond) = &self.cond {
                    yield cond;
                }

                if let Some(update) = &self.update {
                    yield update;
                }

                yield &self.body;
            },
        ))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::Loop(self)
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
    Defer(Block<'a>),
    Loop(Loop<'a>),
}

impl<'a> AstSpan<'a> for Statement<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        match self {
            Statement::Expr(expr, _) => expr.as_span(),
            Statement::FunctionDef(function_def) => function_def.as_span(),
            Statement::Const(const_def) => const_def.as_span(),
            Statement::Local(local_def) => local_def.as_span(),
            Statement::Assignment(ptr_assign) => ptr_assign.as_span(),
            Statement::Typedef(typedef) => typedef.as_span(),
            Statement::Defer(block) => block.as_span(),
            Statement::Loop(inner) => inner.as_span(),
        }
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::from_coroutine(
            #[coroutine]
            || match self {
                Statement::Expr(expr, ..) => yield expr as &dyn AstSpan<'a>,
                Statement::FunctionDef(function_def) => yield function_def,
                Statement::Const(const_def) => yield const_def,
                Statement::Local(local_def) => yield local_def,
                Statement::Assignment(assignment) => yield assignment,
                Statement::Typedef(typedef) => yield typedef,
                Statement::Defer(block) => yield block,
                Statement::Loop(inner) => yield inner,
            },
        ))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::Statement(self)
    }
}

#[derive(Debug, Clone)]
pub struct Block<'a> {
    pub statements: Vec<Statement<'a>>,
    pub captures: DeferedCaptures<'a>,
    // pub return_type: Type,
    pub span: AnnotatedSpan<'a>,
}

impl<'a> AstSpan<'a> for Block<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        self.span
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(self.statements.iter().map(|it| it as &dyn AstSpan<'a>))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::Block(self)
    }
}

#[derive(Debug, Clone)]
pub struct Program<'a> {
    pub directives: Vec<Directive<'a>>,
    pub code: Block<'a>,
    pub span: AnnotatedSpan<'a>,
}

impl<'a> AstSpan<'a> for Program<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        self.span
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::from_coroutine(
            #[coroutine]
            || {
                for directive in &self.directives {
                    yield directive as &dyn AstSpan<'a>;
                }

                yield &self.code;
            },
        ))
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::Program(self)
    }
}

#[derive(Debug, Clone)]
pub enum Directive<'a> {
    Include(&'a Path, AnnotatedSpan<'a>),
}

impl<'a> AstSpan<'a> for Directive<'a> {
    fn as_span(&self) -> AnnotatedSpan<'a> {
        match self {
            Directive::Include(_, span) => *span,
        }
    }

    fn children(&self) -> Box<dyn Iterator<Item = &dyn AstSpan<'a>> + '_> {
        Box::new(iter::empty())
    }

    fn as_ast_node(&self) -> AstNode<'a, '_> {
        AstNode::Directive(self)
    }
}
