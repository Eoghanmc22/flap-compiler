use core::fmt;
use std::fmt::Debug;
use std::iter;
use std::{
    backtrace::Backtrace,
    borrow::Cow,
    error::Error,
    fmt::{Display, Write},
    io,
};

use pest::Span;
use pest::error::InputLocation;
use thiserror::Error;

use crate::ast::{AstSpan, Captures, ComputedSpan, FunctionDef};
use crate::type_check::TypeChecker;
use crate::{
    ast::{
        AnnotatedSpan, Assignment, BinaryOp, Block, ConstDef, Expr, FunctionCall,
        FunctionSignature, IdentRef, LocalDef, PostfixOp, PrefixOp, Statement, Type,
        VariableVersion,
    },
    codegen::{TempoaryIdent, clac::ClacValue},
    parser,
};

pub use parser::PestError;

fn flatten_err(it: impl Display) -> Box<dyn Error + Send + Sync + 'static> {
    struct StringError(String);

    impl Error for StringError {}

    impl fmt::Display for StringError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt::Display::fmt(&self.0, f)
        }
    }

    // Purposefully skip printing "StringError(..)"
    impl fmt::Debug for StringError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt::Display::fmt(&self.0, f)
        }
    }

    Box::new(StringError(it.to_string()))
}

// TODO add path canonicalize error
#[derive(Error, Debug)]
pub enum CompileError<'a> {
    #[error(transparent)]
    Parsing(#[from] ParserError),

    #[error(transparent)]
    TypeCheck(TypeError<'a>),

    #[error(transparent)]
    Codegen(CodegenError<'a>),

    #[error(transparent)]
    Middleware(MiddlewareError<'a>),

    #[error("I/O Error: {0:?}")]
    IoError(#[from] io::Error, Backtrace),

    #[error("fmt Error")]
    FmtError(#[from] fmt::Error, Backtrace),

    #[error("Path Contained Invalid Characters")]
    NonUtf8Path,

    #[error("{}", render(.0, .1, .2, .3))]
    WrapSpan(
        Box<CompileError<'a>>,
        Box<dyn PrintableSpan + 'a>,
        Option<Cow<'a, str>>,
        Vec<(Box<dyn PrintableSpan + 'a>, Cow<'a, str>)>,
    ),
}

impl<'a> From<TypeError<'a>> for CompileError<'a> {
    fn from(value: TypeError<'a>) -> Self {
        Self::TypeCheck(value)
    }
}

impl<'a> From<CodegenError<'a>> for CompileError<'a> {
    fn from(value: CodegenError<'a>) -> Self {
        Self::Codegen(value)
    }
}

impl<'a> From<MiddlewareError<'a>> for CompileError<'a> {
    fn from(value: MiddlewareError<'a>) -> Self {
        Self::Middleware(value)
    }
}

#[derive(Error, Debug)]
pub enum ParserError {
    #[error("{inner}")]
    PestError {
        #[source]
        inner: PestError,
        file_name: String,
        file: String,
    },
}

#[derive(Error, Debug)]
pub enum MiddlewareError<'a> {
    #[error(transparent)]
    TypeCheck(TypeError<'a>),

    #[error(transparent)]
    Codegen(CodegenError<'a>),

    #[error("Array index {index} is out of bounds for length {length}")]
    ArrayIndexOutOfBounds {
        array_type: Type<'a>,
        index_expr: Expr<'a>,
        index: ClacValue,
        length: ClacValue,
        backtrace: Backtrace,
    },
    #[error("Const could not be evaluated at compile time")]
    DynamicConstant {
        constant: ConstDef<'a>,
        backtrace: Backtrace,
    },
    #[error("Can not assign to a place derived from a constant since constants are immutable")]
    MutateConstant {
        assignment: Assignment<'a>,
        backtrace: Backtrace,
    },
    #[error(
        "Call to sizeof_packed on the type {the_type} which does not have a packed repersentation"
    )]
    NoPackedRepr {
        the_type: Type<'a>,
        backtrace: Backtrace,
    },

    #[error("{msg}")]
    UnimplementedFeature { msg: String, backtrace: Backtrace },
    #[error("COMPILER BUG at {0}")]
    CompilerBug(Backtrace),
    #[error("{}", render(.0, .1, .2, .3))]
    WrapSpan(
        Box<MiddlewareError<'a>>,
        Box<dyn PrintableSpan + 'a>,
        Option<Cow<'a, str>>,
        Vec<(Box<dyn PrintableSpan + 'a>, Cow<'a, str>)>,
    ),
}

impl<'a> From<TypeError<'a>> for MiddlewareError<'a> {
    fn from(value: TypeError<'a>) -> Self {
        Self::TypeCheck(value)
    }
}

impl<'a> From<CodegenError<'a>> for MiddlewareError<'a> {
    fn from(value: CodegenError<'a>) -> Self {
        Self::Codegen(value)
    }
}

#[derive(Error, Debug)]
pub enum CodegenError<'a> {
    #[error(transparent)]
    TypeCheck(TypeError<'a>),

    #[error("Encountered Unknown Tempoary {0:?}")]
    UnknownTempoary(TempoaryIdent, Backtrace),
    #[error("Encountered Unknown Local {1} {0}")]
    UnknownLocal(VariableVersion, IdentRef<'a>, Backtrace),
    #[error("Encountered Unknown Constant {1} {0}")]
    UnknownConstant(VariableVersion, IdentRef<'a>, Backtrace),
    #[error("Encountered Unknown function {0}")]
    UnknownFunction(IdentRef<'a>, Backtrace),

    #[error(
        "Attempted to tail call in function `{function}` but it returns a {tail_return_type}, and the calling runction returns a {return_type}, and these types differ in width"
    )]
    BadTailCall {
        function: IdentRef<'a>,
        tail_return_type: Type<'a>,
        return_type: Type<'a>,
        backtrace: Backtrace,
    },
    #[error("Got negative stack offset {offset}")]
    NegativeStackOffset {
        offset: ClacValue,
        backtrace: Backtrace,
    },
    #[error(
        "Bring Up References: expected to load width {expected_width}, actually loaded: {actual_width}"
    )]
    BadBringUp {
        expected_width: ClacValue,
        actual_width: ClacValue,
        backtrace: Backtrace,
    },

    #[error("{msg}")]
    UnimplementedFeature { msg: String, backtrace: Backtrace },
    #[error("COMPILER BUG at {0}")]
    CompilerBug(Backtrace),
    #[error("{}", render(.0, .1, .2, .3))]
    WrapSpan(
        Box<CodegenError<'a>>,
        Box<dyn PrintableSpan + 'a>,
        Option<Cow<'a, str>>,
        Vec<(Box<dyn PrintableSpan + 'a>, Cow<'a, str>)>,
    ),
}

impl<'a> From<TypeError<'a>> for CodegenError<'a> {
    fn from(value: TypeError<'a>) -> Self {
        Self::TypeCheck(value)
    }
}

// TODO: make all fields have something thats as_span?
#[derive(Error, Debug)]
pub enum TypeError<'a> {
    #[error("Typedef `{0}` is defined multiple times")]
    TypedefMultipleDefined(IdentRef<'a>, Backtrace),

    #[error("Variable version {0} is not in scope")]
    VariableVersionNotInScope(VariableVersion, Backtrace),
    #[error("Variable {0} is not in scope")]
    VariableNotInScope(IdentRef<'a>, Backtrace),
    #[error("Function {0} is not in scope")]
    FunctionNotInScope(IdentRef<'a>, Backtrace),
    #[error("Typedef {0} is not in scope")]
    TypedefNotInScope(IdentRef<'a>, Backtrace),
    #[error("The function {} is no_captures, but it captures {:?}", function.function, captures)]
    IllegalCaptures {
        function: FunctionDef<'a>,
        captures: Captures<'a>,
        backtrace: Backtrace,
    },

    #[error("All array elements must be of the same type")]
    ArrayElementsMismatch(Backtrace),
    #[error("Empty arrays are not supported due to type resolution limitations")]
    ArrayEmpty(Backtrace),
    #[error("The operation {lhs_type} {op} {rhs_type} is not implemented for the provided types")]
    BinaryOpBadArgs {
        op: BinaryOp,
        lhs_type: Type<'a>,
        rhs_type: Type<'a>,
        backtrace: Backtrace,
    },
    #[error("The operation {op} {operand_type} is not implemented for the provided type")]
    PrefixOpBadArgs {
        op: PrefixOp<'a>,
        operand_type: Type<'a>,
        backtrace: Backtrace,
    },
    #[error("The operation {operand_type} {op} is not implemented for the provided type")]
    PostfixOpBadArgs {
        op: PostfixOp<'a>,
        operand_type: Type<'a>,
        backtrace: Backtrace,
    },

    #[error("Binary op {lhs_type} {op} {rhs_type}  only support types that are 1 word")]
    BinaryOpWrongWidth {
        op: BinaryOp,
        lhs_type: Type<'a>,
        rhs_type: Type<'a>,
        backtrace: Backtrace,
    },
    #[error("Can not cast from {src_type} to {dst_type} because they differ in width")]
    CastWrongWidth {
        src_type: Type<'a>,
        dst_type: Type<'a>,
        backtrace: Backtrace,
    },
    #[error("Can not dereference a value of the type {operand_type} since its not a pointer type")]
    DereferenceNonPointer {
        operand_type: Type<'a>,
        backtrace: Backtrace,
    },
    #[error("This field {member} does not exist on type {operand_type}")]
    UnknownStructMember {
        operand_type: Type<'a>,
        member: IdentRef<'a>,
        backtrace: Backtrace,
    },
    #[error("This the array index {op} is of type {index_type} but only int is allowed")]
    BadArrayIndexType {
        op: PostfixOp<'a>,
        index_type: Type<'a>,
        backtrace: Backtrace,
    },

    #[error("This function call has the wrong number of arguements for signature {}, (got {}, expected {})", .signature.lsp_render_full(.function.function), .function.parameters.len(), .signature.arguements.len())]
    FunctionCallArgCount {
        function: FunctionCall<'a>,
        signature: FunctionSignature<'a>,
        backtrace: Backtrace,
    },
    #[error(
        "The provided arguement evaluates to type {provided_type}, which is not the expected type {expected_type} for paramater {parm_name}"
    )]
    FunctionCallArgBadType {
        function: FunctionCall<'a>,
        signature: FunctionSignature<'a>,
        parm_name: IdentRef<'a>,
        arg_expr: Expr<'a>,
        expected_type: Type<'a>,
        provided_type: Type<'a>,
        backtrace: Backtrace,
    },
    #[error(
        "This function is supposed to return a {expected_return_type}, but it actually returns {actual_return_type}"
    )]
    BlockReturnsWrongType {
        block: Block<'a>,
        expected_return_type: Type<'a>,
        actual_return_type: Type<'a>,
        last_statement: Option<Statement<'a>>,
        backtrace: Backtrace,
    },

    #[error(
        "Type mismatch in constant definition: expression returns {provided_type}, when a {expected_type} is expected"
    )]
    ConstDefTypeMismatch {
        constant: ConstDef<'a>,
        expected_type: Type<'a>,
        provided_type: Type<'a>,
        backtrace: Backtrace,
    },
    #[error(
        "Type mismatch in local definition: expression returns {provided_type}, when a {expected_type} is expected"
    )]
    LocalDefTypeMismatch {
        local: LocalDef<'a>,
        expected_type: Type<'a>,
        provided_type: Type<'a>,
        backtrace: Backtrace,
    },
    #[error(
        "Type mismatch in assignment: expression returns {expr_type}, when the target place is of type {target_type}"
    )]
    AssignmentTypeMismatch {
        assignment: Assignment<'a>,
        target_type: Type<'a>,
        expr_type: Type<'a>,
        backtrace: Backtrace,
    },
    #[error("The condition is of type {expr_type} when a bool is required")]
    ConditionIsntBool {
        condition: Expr<'a>,
        expr_type: Type<'a>,
        backtrace: Backtrace,
    },

    #[error("LSP INTERNAL TYPECHECKING BREAKPOINT")]
    BreakPoint(TypeChecker<'a>),

    #[error("COMPILER BUG at {0}")]
    CompilerBug(Backtrace),
    #[error("{}", render(.0, .1, .2, .3))]
    WrapSpan(
        Box<TypeError<'a>>,
        Box<dyn PrintableSpan + 'a>,
        Option<Cow<'a, str>>,
        Vec<(Box<dyn PrintableSpan + 'a>, Cow<'a, str>)>,
    ),
}

pub trait SpannedErrorExt<'a>: Sized {
    type OkType;

    fn wrap_span(self, span: impl PrintableSpan + 'a) -> Self;
    fn wrap_span_desc(self, span: impl PrintableSpan + 'a, desc: impl Into<Cow<'a, str>>) -> Self;
    fn wrap_span_desc_with<F, R>(self, span: impl PrintableSpan + 'a, desc: F) -> Self
    where
        R: Into<Cow<'a, str>>,
        F: FnOnce() -> R;

    fn wrap_span_annotations(
        self,
        span: impl PrintableSpan + 'a,
        annotations: Vec<(impl PrintableSpan + 'a, Cow<'a, str>)>,
    ) -> Self;

    fn wrap_span_desc_annotations(
        self,
        span: impl PrintableSpan + 'a,
        desc: impl Into<Cow<'a, str>>,
        annotations: Vec<(impl PrintableSpan + 'a, Cow<'a, str>)>,
    ) -> Self;

    fn flatten(self) -> Result<Self::OkType, Box<dyn Error + Send + Sync + 'static>>;
}

fn render<'a>(
    inner: impl fmt::Display,
    span: &Box<dyn PrintableSpan + '_>,
    description: &Option<Cow<'a, str>>,
    annotations: &[(Box<dyn PrintableSpan + '_>, Cow<'a, str>)],
) -> String {
    let mut string = String::new();

    writeln!(&mut string, "{inner}\n").unwrap();

    let file = span.file_name();
    let (start_line, start_col) = span.start();
    writeln!(&mut string, "{file}:{start_line}:{start_col}\n").unwrap();

    if let Some(description) = description {
        writeln!(&mut string, "{description}\n").unwrap();
    }

    for (idx, line_str) in span.as_str().lines().enumerate() {
        let line = start_line + idx;
        writeln!(&mut string, "{line:4} | {line_str}").unwrap();

        for (anno_span, annotation) in annotations {
            let (anno_start_line, anno_start_col) = anno_span.start();
            let (anno_end_line, anno_end_col) = anno_span.end();

            for (anno_idx, anno_line_span) in anno_span.as_str().lines().enumerate() {
                let anno_line = start_line + anno_idx;

                let col_start = if anno_line == anno_start_line {
                    anno_start_col
                } else {
                    0
                };

                let width = if anno_line == anno_end_line {
                    anno_end_col
                } else {
                    anno_line_span.len()
                };

                if anno_line == line {
                    let mut marker = String::new();

                    marker.push_str(&" ".repeat(col_start + 5));
                    marker.push_str(&"^".repeat(width));

                    if anno_end_line == line {
                        writeln!(&mut string, "{marker} - {annotation}").unwrap();
                    } else {
                        writeln!(&mut string, "{marker}").unwrap();
                    }
                }
            }
        }
    }
    string
}

macro_rules! derive_spanned_error {
    ($($type:ty),*) => {
        $(
            impl<'a, T> SpannedErrorExt<'a> for Result<T, $type> {
                type OkType = T;

                fn wrap_span(self, span: impl PrintableSpan + 'a) -> Self {
                    match self {
                        Ok(inner) => Ok(inner),
                        Err(err) => Err(<$type>::WrapSpan(err.into(), Box::new(span), None, vec![])),
                    }
                }

                fn wrap_span_desc(
                    self,
                    span: impl PrintableSpan + 'a,
                    desc: impl Into<Cow<'a, str>>,
                ) -> Self {
                    match self {
                        Ok(inner) => Ok(inner),
                        Err(err) => Err(<$type>::WrapSpan(
                            err.into(),
                            Box::new(span),
                            Some(desc.into()),
                            vec![],
                        )),
                    }
                }

                fn wrap_span_desc_with<F, R>(self, span: impl PrintableSpan + 'a, desc: F) -> Self
                where
                    R: Into<Cow<'a, str>>,
                    F: FnOnce() -> R,
                {
                    match self {
                        Ok(inner) => Ok(inner),
                        Err(err) => Err(<$type>::WrapSpan(
                            err.into(),
                            Box::new(span),
                            Some((desc)().into()),
                            vec![],
                        )),
                    }
                }

                fn wrap_span_annotations(
                    self,
                    span: impl PrintableSpan + 'a,
                    annotations: Vec<(impl PrintableSpan + 'a, Cow<'a, str>)>,
                ) -> Self {
                    match self {
                        Ok(inner) => Ok(inner),
                        Err(err) => Err(<$type>::WrapSpan(
                            err.into(),
                            Box::new(span),
                            None,
                            annotations.into_iter().map(|(span, desc)| {
                                (Box::new(span) as Box<dyn PrintableSpan>, desc)
                            }).collect()
                        )),
                    }
                }

                fn wrap_span_desc_annotations(
                    self,
                    span: impl PrintableSpan + 'a,
                    desc: impl Into<Cow<'a, str>>,
                    annotations: Vec<(impl PrintableSpan + 'a, Cow<'a, str>)>,
                ) -> Self {
                    match self {
                        Ok(inner) => Ok(inner),
                        Err(err) => Err(<$type>::WrapSpan(
                            err.into(),
                            Box::new(span),
                            Some(desc.into()),
                            annotations.into_iter().map(|(span, desc)| {
                                (Box::new(span) as Box<dyn PrintableSpan>, desc)
                            }).collect()
                        )),
                    }
                }

                fn flatten(self) -> Result<Self::OkType, Box<dyn Error + Send + Sync + 'static>> {
                    match self {
                        Ok(ok) => Ok(ok),
                        Err(err) => Err(flatten_err(err)),
                    }
                }
            }
        )*
    };
}

derive_spanned_error! {
    CompileError<'a>,
    TypeError<'a>,
    CodegenError<'a>,
    MiddlewareError<'a>
}

pub trait IntoSpans: Display {
    fn error_kind(&self) -> &'static str;
    fn spans(&self) -> impl Iterator<Item = (Box<dyn PrintableSpan + '_>, Option<&Cow<'_, str>>)>;
}

impl<'a> IntoSpans for CompileError<'a> {
    fn error_kind(&self) -> &'static str {
        match self {
            CompileError::Parsing(_) => "Parsing Error",
            CompileError::TypeCheck(_) => "TypeCheck Error",
            CompileError::Codegen(_) => "Codegen Error",
            CompileError::Middleware(_) => "Middleware Error",
            CompileError::IoError(..) => "I/O Error",
            CompileError::FmtError(..) => "Fmt Error",
            CompileError::NonUtf8Path => "Bad Path",
            CompileError::WrapSpan(compile_error, ..) => compile_error.error_kind(),
        }
    }

    fn spans(&self) -> impl Iterator<Item = (Box<dyn PrintableSpan + '_>, Option<&Cow<'_, str>>)> {
        iter::from_coroutine(Box::new(
            #[coroutine]
            || match self {
                CompileError::WrapSpan(inner, span, desc, annotations) => {
                    for (span, desc) in (**inner).spans() {
                        yield (span, desc);
                    }

                    yield (span.boxed_clone(), desc.as_ref());

                    for (span, desc) in annotations {
                        yield (span.boxed_clone(), Some(desc));
                    }
                }
                CompileError::Parsing(parser_error) => {
                    for (span, desc) in parser_error.spans() {
                        yield (span, desc);
                    }
                }
                CompileError::TypeCheck(type_error) => {
                    for (span, desc) in type_error.spans() {
                        yield (span, desc);
                    }
                }
                CompileError::Codegen(codegen_error) => {
                    for (span, desc) in codegen_error.spans() {
                        yield (span, desc);
                    }
                }
                CompileError::Middleware(middleware_error) => {
                    for (span, desc) in middleware_error.spans() {
                        yield (span, desc);
                    }
                }
                CompileError::IoError(..) => {}
                CompileError::FmtError(..) => {}
                CompileError::NonUtf8Path => {}
            },
        ))
    }
}

impl IntoSpans for ParserError {
    fn error_kind(&self) -> &'static str {
        match self {
            ParserError::PestError { .. } => "Pest Error",
        }
    }

    fn spans(&self) -> impl Iterator<Item = (Box<dyn PrintableSpan + '_>, Option<&Cow<'_, str>>)> {
        iter::from_coroutine(Box::new(
            #[coroutine]
            || match self {
                ParserError::PestError {
                    inner,
                    file_name,
                    file,
                } => {
                    let (start, end) = match inner.location {
                        InputLocation::Pos(start) => (start, start + 1),
                        InputLocation::Span((start, end)) => (start, end),
                    };

                    if let Some(span) = Span::new(file, start, end) {
                        yield (
                            Box::new(AnnotatedSpan {
                                span,
                                file_name: file_name,
                            }) as Box<dyn PrintableSpan>,
                            None,
                        )
                    }
                }
            },
        ))
    }
}

impl<'a> IntoSpans for TypeError<'a> {
    fn error_kind(&self) -> &'static str {
        match self {
            TypeError::TypedefMultipleDefined(..) => "Typedef Multiple Defined",
            TypeError::VariableVersionNotInScope(..) => "Variable Version Not In Scope",
            TypeError::VariableNotInScope(..) => "Variable Not In Scope",
            TypeError::FunctionNotInScope(..) => "Function Not In Scope",
            TypeError::TypedefNotInScope(..) => "Typedef Not In Scope",
            TypeError::IllegalCaptures { .. } => "Function With #[no_captures] Takes Captures",
            TypeError::ArrayElementsMismatch(..) => "Array Elements Mismatch",
            TypeError::ArrayEmpty(..) => "Array Empty",
            TypeError::BinaryOpBadArgs { .. } => "Binary Op Bad Args",
            TypeError::PrefixOpBadArgs { .. } => "Prefix Op Bad Args",
            TypeError::PostfixOpBadArgs { .. } => "Postfix Op Bad Args",
            TypeError::BinaryOpWrongWidth { .. } => "Binary Op Wrong Width",
            TypeError::CastWrongWidth { .. } => "Cast Wrong Width",
            TypeError::DereferenceNonPointer { .. } => "Dereference Non Pointer",
            TypeError::UnknownStructMember { .. } => "Unknown Struct Member",
            TypeError::BadArrayIndexType { .. } => "Bad Array Index Type",
            TypeError::FunctionCallArgCount { .. } => "Function Call Arg Count",
            TypeError::FunctionCallArgBadType { .. } => "Function Call Arg Bad Type",
            TypeError::BlockReturnsWrongType { .. } => "Block Returns Wrong Type",
            TypeError::ConstDefTypeMismatch { .. } => "Const Def Type Mismatch",
            TypeError::LocalDefTypeMismatch { .. } => "Local Def Type Mismatch",
            TypeError::AssignmentTypeMismatch { .. } => "Assignmen Type Mismatch",
            TypeError::ConditionIsntBool { .. } => "Condition Isnt Bool",
            TypeError::CompilerBug(..) => "Compiler Bug",
            TypeError::WrapSpan(type_error, ..) => type_error.error_kind(),
            TypeError::BreakPoint(..) => "LSP INTERNAL",
        }
    }

    fn spans(&self) -> impl Iterator<Item = (Box<dyn PrintableSpan + '_>, Option<&Cow<'_, str>>)> {
        iter::from_coroutine(Box::new(
            #[coroutine]
            || match self {
                TypeError::WrapSpan(inner, span, desc, annotations) => {
                    for (span, desc) in (**inner).spans() {
                        yield (span, desc);
                    }

                    yield (span.boxed_clone(), desc.as_ref());

                    for (span, desc) in annotations {
                        yield (span.boxed_clone(), Some(desc));
                    }
                }
                TypeError::TypedefMultipleDefined(..) => {}
                TypeError::IllegalCaptures {
                    function, captures, ..
                } => {
                    yield (Box::new(function.as_span()), None);

                    for (_, (_, _, _, span)) in &captures.0 {
                        yield (Box::new(*span), None);
                    }
                }
                TypeError::VariableVersionNotInScope(..) => {}
                TypeError::VariableNotInScope(..) => {}
                TypeError::FunctionNotInScope(..) => {}
                TypeError::TypedefNotInScope(..) => {}
                TypeError::ArrayElementsMismatch(..) => {}
                TypeError::ArrayEmpty(..) => {}
                TypeError::BinaryOpBadArgs { .. } => {}
                TypeError::PrefixOpBadArgs { .. } => {}
                TypeError::PostfixOpBadArgs { .. } => {}
                TypeError::BinaryOpWrongWidth { .. } => {}
                TypeError::CastWrongWidth { .. } => {}
                TypeError::DereferenceNonPointer { .. } => {}
                TypeError::UnknownStructMember { .. } => {}
                TypeError::BadArrayIndexType { .. } => {}
                TypeError::FunctionCallArgCount { function, .. } => {
                    yield (Box::new(function.as_span()), None);
                }
                TypeError::FunctionCallArgBadType {
                    function, arg_expr, ..
                } => {
                    yield (Box::new(arg_expr.as_span()), None);
                    yield (Box::new(function.as_span()), None);
                }
                TypeError::BlockReturnsWrongType {
                    block,
                    last_statement,
                    ..
                } => {
                    if let Some(last_statement) = last_statement {
                        yield (Box::new(last_statement.as_span()), None);
                    }
                    yield (Box::new(block.as_span()), None);
                }
                TypeError::ConstDefTypeMismatch { constant, .. } => {
                    yield (Box::new(constant.as_span()), None)
                }
                TypeError::LocalDefTypeMismatch { local, .. } => {
                    yield (Box::new(local.as_span()), None)
                }
                TypeError::AssignmentTypeMismatch { assignment, .. } => {
                    yield (Box::new(assignment.as_span()), None)
                }
                TypeError::ConditionIsntBool { condition, .. } => {
                    yield (Box::new(condition.as_span()), None)
                }
                TypeError::CompilerBug(..) => {}
                TypeError::BreakPoint(..) => {}
            },
        ))
    }
}

impl<'a> IntoSpans for CodegenError<'a> {
    fn error_kind(&self) -> &'static str {
        match self {
            CodegenError::TypeCheck(..) => "Type Error",
            CodegenError::UnknownTempoary(..) => "Unknown Tempoary",
            CodegenError::UnknownLocal(..) => "Unknown Local",
            CodegenError::UnknownConstant(..) => "Unknown Constant",
            CodegenError::UnknownFunction(..) => "Unknown Function",
            CodegenError::BadTailCall { .. } => "Bad Tail Call",
            CodegenError::NegativeStackOffset { .. } => "Negative Stack Offset",
            CodegenError::BadBringUp { .. } => "Bad Bring Up",
            CodegenError::UnimplementedFeature { .. } => "Unimplemented Feature",
            CodegenError::CompilerBug(..) => "Compiler Bug",
            CodegenError::WrapSpan(codegen_error, ..) => codegen_error.error_kind(),
        }
    }

    fn spans(&self) -> impl Iterator<Item = (Box<dyn PrintableSpan + '_>, Option<&Cow<'_, str>>)> {
        iter::from_coroutine(Box::new(
            #[coroutine]
            || match self {
                CodegenError::WrapSpan(inner, span, desc, annotations) => {
                    for (span, desc) in (**inner).spans() {
                        yield (span, desc);
                    }

                    yield (span.boxed_clone(), desc.as_ref());

                    for (span, desc) in annotations {
                        yield (span.boxed_clone(), Some(desc));
                    }
                }
                CodegenError::TypeCheck(type_error) => {
                    for (span, desc) in type_error.spans() {
                        yield (span, desc);
                    }
                }
                _ => {}
            },
        ))
    }
}

impl<'a> IntoSpans for MiddlewareError<'a> {
    fn error_kind(&self) -> &'static str {
        match self {
            MiddlewareError::TypeCheck(..) => "Type Error",
            MiddlewareError::Codegen(..) => "Codegen Error",
            MiddlewareError::ArrayIndexOutOfBounds { .. } => "Array Index Out Of Bounds",
            MiddlewareError::DynamicConstant { .. } => "Dynamic Constant",
            MiddlewareError::MutateConstant { .. } => "Mutate Constant",
            MiddlewareError::NoPackedRepr { .. } => "No Packed Repr",
            MiddlewareError::UnimplementedFeature { .. } => "Unimplemented Feature",
            MiddlewareError::CompilerBug(..) => "Compiler Bug",
            MiddlewareError::WrapSpan(middleware_error, ..) => middleware_error.error_kind(),
        }
    }

    fn spans(&self) -> impl Iterator<Item = (Box<dyn PrintableSpan + '_>, Option<&Cow<'_, str>>)> {
        iter::from_coroutine(Box::new(
            #[coroutine]
            || match self {
                MiddlewareError::WrapSpan(inner, span, desc, annotations) => {
                    for (span, desc) in (**inner).spans() {
                        yield (span, desc);
                    }

                    yield (span.boxed_clone(), desc.as_ref());

                    for (span, desc) in annotations {
                        yield (span.boxed_clone(), Some(desc));
                    }
                }
                MiddlewareError::TypeCheck(type_error) => {
                    for (span, desc) in type_error.spans() {
                        yield (span, desc);
                    }
                }
                MiddlewareError::Codegen(codegen_error) => {
                    for (span, desc) in codegen_error.spans() {
                        yield (span, desc);
                    }
                }
                MiddlewareError::ArrayIndexOutOfBounds { index_expr, .. } => {
                    yield (Box::new(index_expr.as_span()), None);
                }
                MiddlewareError::DynamicConstant { constant, .. } => {
                    yield (Box::new(constant.as_span()), None);
                }
                MiddlewareError::MutateConstant { assignment, .. } => {
                    yield (Box::new(assignment.as_span()), None);
                }
                MiddlewareError::NoPackedRepr { .. } => {}
                MiddlewareError::UnimplementedFeature { .. } => {}
                MiddlewareError::CompilerBug(..) => {}
            },
        ))
    }
}

pub trait PrintableSpan: Debug + Send + Sync {
    fn as_str(&self) -> &str;
    fn file_name(&self) -> &str;
    fn start(&self) -> (usize, usize);
    fn end(&self) -> (usize, usize);

    fn boxed_clone(&self) -> Box<dyn PrintableSpan + '_>;
}

impl PrintableSpan for AnnotatedSpan<'_> {
    fn as_str(&self) -> &str {
        self.span.as_str()
    }

    fn file_name(&self) -> &str {
        &self.file_name
    }

    fn start(&self) -> (usize, usize) {
        self.span.start_pos().line_col()
    }

    fn end(&self) -> (usize, usize) {
        self.span.end_pos().line_col()
    }

    fn boxed_clone(&self) -> Box<dyn PrintableSpan + '_> {
        Box::new(self.clone())
    }
}

impl PrintableSpan for ComputedSpan<'_> {
    fn as_str(&self) -> &str {
        &self.content
    }

    fn file_name(&self) -> &str {
        &self.file_name
    }

    fn start(&self) -> (usize, usize) {
        self.start
    }

    fn end(&self) -> (usize, usize) {
        self.end
    }

    fn boxed_clone(&self) -> Box<dyn PrintableSpan + '_> {
        Box::new(self.clone())
    }
}
