use core::fmt;
use std::{
    backtrace::Backtrace,
    borrow::Cow,
    error::Error,
    fmt::{Display, Write},
    io,
};

use thiserror::Error;

use crate::{
    ast::{
        AnnotatedSpan, Assignment, BinaryOp, Block, ConstDef, Expr, FunctionCall,
        FunctionSignature, IdentRef, LocalDef, PostfixOp, PrefixOp, Statement, Type,
        VariableVersion,
    },
    codegen::{TempoaryIdent, clac::ClacValue},
    parser,
};

pub use parser::ParsingError;

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
    Parsing(#[from] ParsingError),

    #[error(transparent)]
    TypeCheck(TypeError<'a>),

    #[error(transparent)]
    Codegen(CodegenError<'a>),

    #[error(transparent)]
    Middleware(MiddlewareError<'a>),

    #[error("I/O Error")]
    IoError(#[from] io::Error, Backtrace),

    #[error("fmt Error")]
    FmtError(#[from] fmt::Error, Backtrace),

    #[error("Path Contained Invalid Characters")]
    NonUtf8Path,

    #[error("{}", render(.0, .1, .2, .3))]
    WrapSpan(
        Box<CompileError<'a>>,
        AnnotatedSpan<'a>,
        Option<Cow<'a, str>>,
        Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
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
        cosntant: ConstDef<'a>,
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
        AnnotatedSpan<'a>,
        Option<Cow<'a, str>>,
        Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
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
        AnnotatedSpan<'a>,
        Option<Cow<'a, str>>,
        Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
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

    #[error("COMPILER BUG at {0}")]
    CompilerBug(Backtrace),
    #[error("{}", render(.0, .1, .2, .3))]
    WrapSpan(
        Box<TypeError<'a>>,
        AnnotatedSpan<'a>,
        Option<Cow<'a, str>>,
        Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
    ),
}

pub trait SpannedErrorExt<'a>: Sized {
    type OkType;

    fn wrap_span(self, span: AnnotatedSpan<'a>) -> Self;
    fn wrap_span_desc(self, span: AnnotatedSpan<'a>, desc: impl Into<Cow<'a, str>>) -> Self;
    fn wrap_span_desc_with<F, R>(self, span: AnnotatedSpan<'a>, desc: F) -> Self
    where
        R: Into<Cow<'a, str>>,
        F: FnOnce() -> R;

    fn wrap_span_annotations(
        self,
        span: AnnotatedSpan<'a>,
        annotations: Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
    ) -> Self;

    fn wrap_span_desc_annotations(
        self,
        span: AnnotatedSpan<'a>,
        desc: impl Into<Cow<'a, str>>,
        annotations: Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
    ) -> Self;

    fn flatten(self) -> Result<Self::OkType, Box<dyn Error + Send + Sync + 'static>>;
}

fn render<'a>(
    inner: impl fmt::Display,
    span: &AnnotatedSpan,
    description: &Option<Cow<'a, str>>,
    annotations: &[(AnnotatedSpan, Cow<'a, str>)],
) -> String {
    let mut string = String::new();

    writeln!(&mut string, "{inner}\n").unwrap();

    let file = span.file_name;
    let (line, col) = span.span.start_pos().line_col();
    writeln!(&mut string, "{file}:{line}:{col}\n").unwrap();

    if let Some(description) = description {
        writeln!(&mut string, "{description}\n").unwrap();
    }

    for line_span in span.span.lines_span() {
        let (line, _col) = line_span.start_pos().line_col();
        write!(&mut string, "{line:4} | {}", line_span.as_str()).unwrap();

        for (anno_span, annotation) in annotations {
            for anno_line_span in anno_span.span.lines_span() {
                let (anno_line, anno_col_start) = anno_line_span.start_pos().line_col();
                let width = anno_line_span.end_pos().pos() - anno_line_span.start_pos().pos();

                if anno_line == line {
                    let mut marker = String::new();

                    marker.push_str(&" ".repeat(anno_col_start + 5));
                    marker.push_str(&"^".repeat(width));

                    for line in annotation.lines() {
                        writeln!(&mut string, "{marker} - {line}").unwrap();
                    }
                }
            }
        }
    }
    string
}

impl<'a, T> SpannedErrorExt<'a> for Result<T, CompileError<'a>> {
    type OkType = T;

    fn wrap_span(self, span: AnnotatedSpan<'a>) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(CompileError::WrapSpan(err.into(), span, None, vec![])),
        }
    }

    fn wrap_span_desc(self, span: AnnotatedSpan<'a>, desc: impl Into<Cow<'a, str>>) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(CompileError::WrapSpan(
                err.into(),
                span,
                Some(desc.into()),
                vec![],
            )),
        }
    }

    fn wrap_span_desc_with<F, R>(self, span: AnnotatedSpan<'a>, desc: F) -> Self
    where
        R: Into<Cow<'a, str>>,
        F: FnOnce() -> R,
    {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(CompileError::WrapSpan(
                err.into(),
                span,
                Some((desc)().into()),
                vec![],
            )),
        }
    }

    fn wrap_span_annotations(
        self,
        span: AnnotatedSpan<'a>,
        annotations: Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
    ) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(CompileError::WrapSpan(err.into(), span, None, annotations)),
        }
    }

    fn wrap_span_desc_annotations(
        self,
        span: AnnotatedSpan<'a>,
        desc: impl Into<Cow<'a, str>>,
        annotations: Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
    ) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(CompileError::WrapSpan(
                err.into(),
                span,
                Some(desc.into()),
                annotations,
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

impl<'a, T> SpannedErrorExt<'a> for Result<T, TypeError<'a>> {
    type OkType = T;

    fn wrap_span(self, span: AnnotatedSpan<'a>) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(TypeError::WrapSpan(err.into(), span, None, vec![])),
        }
    }

    fn wrap_span_desc(self, span: AnnotatedSpan<'a>, desc: impl Into<Cow<'a, str>>) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(TypeError::WrapSpan(
                err.into(),
                span,
                Some(desc.into()),
                vec![],
            )),
        }
    }

    fn wrap_span_desc_with<F, R>(self, span: AnnotatedSpan<'a>, desc: F) -> Self
    where
        R: Into<Cow<'a, str>>,
        F: FnOnce() -> R,
    {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(TypeError::WrapSpan(
                err.into(),
                span,
                Some((desc)().into()),
                vec![],
            )),
        }
    }

    fn wrap_span_annotations(
        self,
        span: AnnotatedSpan<'a>,
        annotations: Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
    ) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(TypeError::WrapSpan(err.into(), span, None, annotations)),
        }
    }

    fn wrap_span_desc_annotations(
        self,
        span: AnnotatedSpan<'a>,
        desc: impl Into<Cow<'a, str>>,
        annotations: Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
    ) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(TypeError::WrapSpan(
                err.into(),
                span,
                Some(desc.into()),
                annotations,
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

impl<'a, T> SpannedErrorExt<'a> for Result<T, CodegenError<'a>> {
    type OkType = T;

    fn wrap_span(self, span: AnnotatedSpan<'a>) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(CodegenError::WrapSpan(err.into(), span, None, vec![])),
        }
    }

    fn wrap_span_desc(self, span: AnnotatedSpan<'a>, desc: impl Into<Cow<'a, str>>) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(CodegenError::WrapSpan(
                err.into(),
                span,
                Some(desc.into()),
                vec![],
            )),
        }
    }

    fn wrap_span_desc_with<F, R>(self, span: AnnotatedSpan<'a>, desc: F) -> Self
    where
        R: Into<Cow<'a, str>>,
        F: FnOnce() -> R,
    {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(CodegenError::WrapSpan(
                err.into(),
                span,
                Some((desc)().into()),
                vec![],
            )),
        }
    }

    fn wrap_span_annotations(
        self,
        span: AnnotatedSpan<'a>,
        annotations: Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
    ) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(CodegenError::WrapSpan(err.into(), span, None, annotations)),
        }
    }

    fn wrap_span_desc_annotations(
        self,
        span: AnnotatedSpan<'a>,
        desc: impl Into<Cow<'a, str>>,
        annotations: Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
    ) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(CodegenError::WrapSpan(
                err.into(),
                span,
                Some(desc.into()),
                annotations,
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

impl<'a, T> SpannedErrorExt<'a> for Result<T, MiddlewareError<'a>> {
    type OkType = T;

    fn wrap_span(self, span: AnnotatedSpan<'a>) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(MiddlewareError::WrapSpan(err.into(), span, None, vec![])),
        }
    }

    fn wrap_span_desc(self, span: AnnotatedSpan<'a>, desc: impl Into<Cow<'a, str>>) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(MiddlewareError::WrapSpan(
                err.into(),
                span,
                Some(desc.into()),
                vec![],
            )),
        }
    }

    fn wrap_span_desc_with<F, R>(self, span: AnnotatedSpan<'a>, desc: F) -> Self
    where
        R: Into<Cow<'a, str>>,
        F: FnOnce() -> R,
    {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(MiddlewareError::WrapSpan(
                err.into(),
                span,
                Some((desc)().into()),
                vec![],
            )),
        }
    }

    fn wrap_span_annotations(
        self,
        span: AnnotatedSpan<'a>,
        annotations: Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
    ) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(MiddlewareError::WrapSpan(
                err.into(),
                span,
                None,
                annotations,
            )),
        }
    }

    fn wrap_span_desc_annotations(
        self,
        span: AnnotatedSpan<'a>,
        desc: impl Into<Cow<'a, str>>,
        annotations: Vec<(AnnotatedSpan<'a>, Cow<'a, str>)>,
    ) -> Self {
        match self {
            Ok(inner) => Ok(inner),
            Err(err) => Err(MiddlewareError::WrapSpan(
                err.into(),
                span,
                Some(desc.into()),
                annotations,
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
