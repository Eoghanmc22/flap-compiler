use std::{
    backtrace::Backtrace,
    collections::{BTreeMap, HashMap, HashSet},
    fmt::{self, Debug, Display},
    sync::{
        Arc,
        atomic::{AtomicI64, AtomicU64, Ordering},
    },
};

use crate::{
    ast::{
        AnnotatedSpan, Arguement, Assignment, AstSpan, BinaryOp, Block, CaptureKind, Captures,
        ConstDef, DeferedAddress, DeferedCaptures, DeferedType, DeferedVersion, Expr,
        FunctionAttribute, FunctionCall, FunctionDef, FunctionSignature, IdentRef, IfCase, IfExpr,
        LocalDef, Loop, PostfixOp, PrefixOp, Punctuation, Statement, Type, Typedef, Value,
        VariableVersion,
    },
    codegen::{builtins::clac_builtins, clac::ClacValue},
    error::{SpannedErrorExt as _, TypeError},
};

type Result<'a, T, E = TypeError<'a>> = std::result::Result<T, E>;

pub const GLOBAL_ARENA_START: ClacValue = 0x67670000;
pub const PAGE_SIZE: ClacValue = 4096;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariableKind {
    Local,
    Constant,
    Capture(CaptureKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, PartialOrd, Ord)]
pub enum FrameKind {
    #[default]
    Regular,
    Phantom,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, PartialOrd, Ord)]
pub enum FunctionKind {
    #[default]
    Regular,
    LangItem,
}

#[derive(Debug, Clone)]
pub struct TypeCheckerFrame<'a> {
    pub variables: HashMap<IdentRef<'a>, VariableVersion>,
    pub variables_versioned:
        HashMap<VariableVersion, (IdentRef<'a>, Type<'a>, VariableKind, AnnotatedSpan<'a>)>,
    pub functions: HashMap<IdentRef<'a>, (FunctionSignature<'a>, AnnotatedSpan<'a>)>,

    pub frame_kind: FrameKind,
    pub capture_kind: CaptureKind,
}

impl<'a> TypeCheckerFrame<'a> {
    pub fn get_captures(&self) -> Captures<'a> {
        Captures(
            self.variables_versioned
                .iter()
                .filter_map(|(version, (ident, data_type, kind, span))| match kind {
                    VariableKind::Capture(capture_kind) => {
                        Some((*version, (data_type.clone(), *ident, *capture_kind, *span)))
                    }
                    _ => None,
                })
                .collect(),
        )
    }
}

#[derive(Debug, Clone)]
pub struct TypeChecker<'a> {
    pub scope_stack: Vec<TypeCheckerFrame<'a>>,
    pub typedefs: HashMap<IdentRef<'a>, (Type<'a>, AnnotatedSpan<'a>)>,
    pub lang_items: HashMap<IdentRef<'a>, (FunctionSignature<'a>, AnnotatedSpan<'a>)>,
    version_counter: Arc<AtomicU64>,
    address_counter: Arc<AtomicI64>,
    break_point: Option<usize>,
}

impl Display for TypeChecker<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeChecker {{ scope: [ ")?;

        let mut already_printed = HashSet::new();
        for frame in self.scope_stack.iter().rev() {
            for (version, (ident, data_type, kind, _span)) in &frame.variables_versioned {
                if already_printed.insert(ident) {
                    write!(f, "{} {}{} ({:?}); ", data_type, ident, version, kind)?;
                }
            }
        }

        write!(f, "] }}")
    }
}

impl Default for TypeChecker<'_> {
    fn default() -> Self {
        let mut type_checker = Self {
            scope_stack: Vec::default(),
            typedefs: HashMap::default(),
            lang_items: HashMap::default(),
            version_counter: Arc::default(),
            address_counter: Arc::new(AtomicI64::new(GLOBAL_ARENA_START)),
            break_point: None,
        };

        for (ident, (_code, mut sig)) in clac_builtins() {
            type_checker.define_function(
                ident,
                &mut sig,
                AnnotatedSpan::builtin(),
                FunctionKind::Regular,
                |_| {},
            );
        }

        type_checker.push_scope_frame(FrameKind::Regular, CaptureKind::Read);

        type_checker
    }
}

impl<'a> TypeChecker<'a> {
    fn push_scope_frame(
        &mut self,
        frame_kind: FrameKind,
        capture_kind: CaptureKind,
    ) -> &mut TypeCheckerFrame<'a> {
        let last_frame_kind = self
            .scope_stack
            .last()
            .map(|it| it.frame_kind)
            .unwrap_or(FrameKind::Regular);

        self.scope_stack.push_mut(TypeCheckerFrame {
            variables: Default::default(),
            variables_versioned: Default::default(),
            functions: Default::default(),
            frame_kind: frame_kind.max(last_frame_kind),
            capture_kind,
        })
    }

    fn pop_scope_frame(&mut self) -> Option<TypeCheckerFrame<'a>> {
        assert!(
            self.scope_stack.len() >= 2,
            "Attempted to pop builtins frame of type checker"
        );

        self.scope_stack.pop()
    }

    fn top_scope_frame(&mut self) -> &mut TypeCheckerFrame<'a> {
        if self.scope_stack.is_empty() {
            self.push_scope_frame(FrameKind::Regular, CaptureKind::Read)
        } else {
            self.scope_stack.last_mut().unwrap()
        }
    }

    pub fn define_function<T, F: FnMut(&mut Self) -> T>(
        &mut self,
        ident: IdentRef<'a>,
        signature: &mut FunctionSignature<'a>,
        span: AnnotatedSpan<'a>,
        kind: FunctionKind,
        mut scope: F,
    ) -> (T, TypeCheckerFrame<'a>) {
        self.top_scope_frame()
            .functions
            .insert(ident, (signature.clone(), span));

        let res = self.define_scope(
            |ctx| {
                for arguement in &mut signature.arguements {
                    let Arguement {
                        arg_type,
                        arg_name,
                        version,
                        span,
                    } = arguement;

                    let actual_version =
                        ctx.define_variable(arg_name, arg_type.clone(), VariableKind::Local, *span);
                    *version = DeferedVersion::ResolvedVersion(actual_version);
                }

                // Pass 1, Goal: compute what this captures
                (scope)(ctx);

                // Compute captures
                signature.captures =
                    DeferedCaptures::ResolvedCaptures(ctx.top_scope_frame().get_captures());

                // Pass 2, Goal: propagate info about the current captures to recursive call sites
                let parent = ctx.scope_stack.len() - 2;
                ctx.scope_stack[parent]
                    .functions
                    .insert(ident, (signature.clone(), span));
                (scope)(ctx)
            },
            FrameKind::Regular,
            CaptureKind::Read,
        );

        if let FunctionKind::LangItem = kind {
            self.lang_items.insert(ident, (signature.clone(), span));
        }

        res
    }

    pub fn define_scope<T, F: FnOnce(&mut Self) -> T>(
        &mut self,
        scope: F,
        frame_kind: FrameKind,
        capture_kind: CaptureKind,
    ) -> (T, TypeCheckerFrame<'a>) {
        self.push_scope_frame(frame_kind, capture_kind);
        let ret = (scope)(self);
        let frame = self.pop_scope_frame().unwrap();

        (ret, frame)
    }

    pub fn allocate_version(&self) -> VariableVersion {
        VariableVersion(self.version_counter.fetch_add(1, Ordering::Relaxed))
    }

    pub fn allocate_address(&self, width: ClacValue) -> ClacValue {
        self.address_counter
            .fetch_add(width.next_multiple_of(16), Ordering::SeqCst)
    }
    pub fn allocate_address_type(&self, var_type: &Type<'a>) -> Result<'a, ClacValue> {
        Ok(self.allocate_address(var_type.width(self)?))
    }

    pub fn define_variable(
        &mut self,
        ident: IdentRef<'a>,
        var_type: Type<'a>,
        kind: VariableKind,
        span: AnnotatedSpan<'a>,
    ) -> VariableVersion {
        let version = self.allocate_version();

        let frame = self.top_scope_frame();
        frame.variables.insert(ident, version);
        frame
            .variables_versioned
            .insert(version, (ident, var_type, kind, span));

        version
    }

    pub fn define_type(
        &mut self,
        ident: IdentRef<'a>,
        type_alias: Type<'a>,
        span: AnnotatedSpan<'a>,
    ) -> Result<'a, ()> {
        let res = self.typedefs.insert(ident, (type_alias, span));

        match res {
            Some(_) => Err(TypeError::TypedefMultipleDefined(
                ident.into(),
                Backtrace::force_capture(),
            )),
            None => Ok(()),
        }
    }

    pub fn frame_kind(&mut self) -> FrameKind {
        self.top_scope_frame().frame_kind
    }

    pub fn capture_kind(&mut self) -> CaptureKind {
        self.top_scope_frame().capture_kind
    }

    pub fn lookup_function(
        &self,
        ident: IdentRef<'a>,
    ) -> Result<'a, (&FunctionSignature<'a>, AnnotatedSpan<'a>)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((sig, span)) = frame.functions.get(&ident) {
                return Ok((sig, *span));
            }
        }

        Err(TypeError::FunctionNotInScope(
            ident.into(),
            Backtrace::capture(),
        ))
    }

    // TODO: need a way to repersent scopes where captures are not taken such as arguements to
    // sizeof() expressions
    pub fn lookup_variable_versioned(
        &mut self,
        var: VariableVersion,
        capture_kind: CaptureKind,
    ) -> Result<'a, (Type<'a>, VariableVersion, AnnotatedSpan<'a>)> {
        let frame_kind = self.frame_kind();

        for (idx, frame) in self.scope_stack.iter().rev().enumerate() {
            if let Some((
                ident,
                var_type,
                kind @ (VariableKind::Local | VariableKind::Constant),
                span,
            )) = frame.variables_versioned.get(&var)
            {
                let ident = *ident;
                let var_type = var_type.clone();
                let span = *span;

                if let FrameKind::Regular = frame_kind
                    && let VariableKind::Local = kind
                {
                    for frame in self.scope_stack.iter_mut().rev().take(idx) {
                        let (_, _, VariableKind::Capture(prev_mode), _span) =
                            frame.variables_versioned.entry(var).or_insert((
                                ident,
                                var_type.clone(),
                                VariableKind::Capture(capture_kind),
                                span,
                            ))
                        else {
                            unreachable!()
                        };

                        *prev_mode = (*prev_mode).max(capture_kind)
                    }
                }

                return Ok((var_type, var, span));
            }
        }

        Err(TypeError::VariableVersionNotInScope(
            var,
            Backtrace::capture(),
        ))
    }

    // TODO: need a way to repersent scopes where captures are not taken such as arguements to
    // sizeof() expressions
    pub fn lookup_variable(
        &mut self,
        var: IdentRef<'a>,
    ) -> Result<'a, (Type<'a>, VariableVersion, AnnotatedSpan<'a>)> {
        let capture_kind = self.capture_kind();

        for frame in self.scope_stack.iter().rev() {
            if let Some(version) = frame.variables.get(var) {
                return self.lookup_variable_versioned(*version, capture_kind);
            }
        }

        Err(TypeError::VariableNotInScope(
            var.into(),
            Backtrace::capture(),
        ))
    }

    pub fn set_break_point<T: ?Sized>(&mut self, break_point: *const T) {
        self.break_point = Some(break_point as *const () as usize)
    }

    fn check_break_point<T>(&mut self, break_point: *const T) -> Result<'a, ()> {
        if let Some(goal) = self.break_point {
            if goal == break_point as usize {
                return Err(TypeError::BreakPoint(self.clone()));
            }
        }

        Ok(())
    }
}

pub trait TypeCheck<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>>;
}

impl<'a> TypeCheck<'a> for Value<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        Ok(self.compute_type())
    }
}

impl<'a> TypeCheck<'a> for Expr<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        match self {
            Expr::SizeOfType(..) => Ok(Type::Int),
            Expr::SizeOfExpr(inner_expr, defered_type, _mode, _span) => {
                let (resolved_type, _frame) = ctx.define_scope(
                    |ctx| inner_expr.check_and_resolve_types(ctx),
                    FrameKind::Phantom,
                    CaptureKind::Read,
                );

                *defered_type = DeferedType::ResolvedType(resolved_type?);

                Ok(Type::Int)
            }
            Expr::GlobalOfType(global_type, address, _) => {
                *address = DeferedAddress::ResolvedAddress(ctx.allocate_address_type(global_type)?);

                Ok(Type::Pointer(global_type.clone().into()))
            }
            Expr::GlobalOfExpr(width_expr, span) => {
                let (resolved_type, _frame) = ctx.define_scope(
                    |ctx| width_expr.check_and_resolve_types(ctx),
                    FrameKind::Phantom,
                    CaptureKind::Read,
                );

                // Cant resolve width yet

                let resolved_type = resolved_type?;
                if !resolved_type.compatible_with(&Type::Int, ctx)? {
                    return Err(TypeError::FunctionCallArgBadType {
                        arg_expr: (**width_expr).clone(),
                        function: FunctionCall {
                            function: "global",
                            parameters: vec![(**width_expr).clone()],
                            span: *span,
                        },
                        signature: FunctionSignature {
                            arguements: vec![Arguement {
                                arg_type: Type::Int,
                                arg_name: "width_bytes",
                                version: DeferedVersion::UnresolvedVersion,
                                span: AnnotatedSpan::builtin(),
                            }],
                            captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                            return_type: Type::Pointer(Type::Void.into()),
                            span: AnnotatedSpan::builtin(),
                        },
                        parm_name: "width_bytes",
                        expected_type: Type::Int,
                        provided_type: resolved_type,
                        backtrace: Backtrace::capture(),
                    })
                    .wrap_span(*span);
                }

                Ok(Type::Pointer(Type::Void.into()))
            }
            Expr::Value(value, span) => value
                .check_and_resolve_types(ctx)
                .wrap_span_desc(*span, "Could not type check expr value"),
            Expr::Variable(ident, defered_version, span) => {
                let (var_type, version, _span) =
                    ctx.lookup_variable(ident).wrap_span_desc_with(*span, || {
                        format!("Could not find identifier: `{ident:?}`")
                    })?;

                *defered_version = DeferedVersion::ResolvedVersion(version);

                Ok(var_type)
            }
            Expr::Struct(map, defered_type, _span) => {
                let map = map
                    .into_iter()
                    .map(|(key, expr)| Ok((*key, expr.check_and_resolve_types(ctx)?)))
                    .collect::<Result<BTreeMap<_, _>>>()?;

                *defered_type = DeferedType::ResolvedType(Type::Struct(map.clone()));

                Ok(Type::Struct(map))
            }
            Expr::NamedTuple(map, defered_type, _span) => {
                let map = map
                    .into_iter()
                    .map(|(key, expr)| Ok((*key, expr.check_and_resolve_types(ctx)?)))
                    .collect::<Result<Vec<_>>>()?;

                *defered_type = DeferedType::ResolvedType(Type::NamedTuple(map.clone()));

                Ok(Type::NamedTuple(map))
            }
            Expr::Array(exprs, defered_type, span) => {
                let types = exprs
                    .into_iter()
                    .map(|expr| Ok((expr.as_span(), expr.check_and_resolve_types(ctx)?)))
                    .collect::<Result<Vec<_>>>()?;

                let mut inner_type: Option<(AnnotatedSpan, &Type)> = None;
                for (span, expr_type) in &types {
                    if let Some((first, inner_type)) = inner_type {
                        if !inner_type.compatible_with(expr_type, ctx)? {
                            return Err(TypeError::ArrayElementsMismatch(Backtrace::capture()))
                                .wrap_span_annotations(
                                    *span,
                                    vec![
                                        (first, format!("has the type `{inner_type:?}`").into()),
                                        (
                                            *span,
                                            format!("has differing type `{expr_type:?}`").into(),
                                        ),
                                    ],
                                );
                        }
                    } else {
                        inner_type = Some((*span, expr_type));
                    }
                }

                if let Some((_, inner_type)) = inner_type {
                    let arr_typ = Type::Array(inner_type.clone().into(), exprs.len() as ClacValue);

                    *defered_type = DeferedType::ResolvedType(arr_typ.clone());
                    Ok(arr_typ)
                } else {
                    return Err(TypeError::ArrayEmpty(Backtrace::capture())).wrap_span(*span);
                }
            }
            Expr::BinaryOp {
                op,
                left,
                right,
                span,
                left_type,
                right_type,
                op_span,
            } => {
                // eval args as read only
                let (result, _frame) = ctx.define_scope(
                    |ctx| {
                        let left_type_computed =
                            left.check_and_resolve_types(ctx)?.resolve_once(ctx)?;
                        let right_type_computed =
                            right.check_and_resolve_types(ctx)?.resolve_once(ctx)?;
                        Ok((left_type_computed, right_type_computed))
                    },
                    FrameKind::Regular,
                    CaptureKind::Read,
                );
                let (left_type_computed, right_type_computed) = result?;

                *left_type = DeferedType::ResolvedType(left_type_computed.clone());
                *right_type = DeferedType::ResolvedType(right_type_computed.clone());

                if left_type_computed.width(ctx)? != 1 || right_type_computed.width(ctx)? != 1 {
                    let lhs_width = left_type_computed.width(ctx)?;
                    let rhs_width = right_type_computed.width(ctx)?;

                    return Err(TypeError::BinaryOpWrongWidth {
                        op: op.clone(),
                        lhs_type: left_type_computed,
                        rhs_type: right_type_computed,
                        backtrace: Backtrace::capture(),
                    })
                    .wrap_span_annotations(
                        *span,
                        vec![(
                            *op_span,
                            format!("lhs has width {}, rhs has width {}", lhs_width, rhs_width)
                                .into(),
                        )],
                    );
                }

                let (valid_types, output_type) =
                    match (&op, &left_type_computed, &right_type_computed) {
                        (
                            BinaryOp::Add
                            | BinaryOp::Sub
                            | BinaryOp::Mul
                            | BinaryOp::Div
                            | BinaryOp::Mod
                            | BinaryOp::Pow
                            | BinaryOp::BShr
                            | BinaryOp::BShl
                            | BinaryOp::BAnd
                            | BinaryOp::BOr
                            | BinaryOp::BXor,
                            left @ (Type::Int | Type::Char),
                            right,
                        ) => (left.compatible_with(right, ctx)?, left.clone()),
                        (BinaryOp::Add | BinaryOp::Sub, left @ Type::Pointer(_), Type::Int) => {
                            (true, left.clone())
                        }
                        (BinaryOp::Sub, Type::Pointer(left), Type::Pointer(right)) => {
                            (left.compatible_with(right, ctx)?, Type::Int)
                        }
                        (
                            BinaryOp::Eq
                            | BinaryOp::Ne
                            | BinaryOp::Le
                            | BinaryOp::Ge
                            | BinaryOp::Lt
                            | BinaryOp::Gt,
                            left,
                            right,
                        ) => (left.compatible_with(right, ctx)?, Type::Bool),
                        (BinaryOp::LAnd | BinaryOp::LOr, Type::Bool, Type::Bool) => {
                            (true, Type::Bool)
                        }
                        _ => (false, Type::Void),
                    };

                if !valid_types {
                    let annotations = vec![(
                        *op_span,
                        format!(
                            "lhs has the type `{left_type_computed:?}` and rhs has the type `{right_type_computed:?}`, which is not permitted"
                        )
                        .into(),
                    )];

                    return Err(TypeError::BinaryOpBadArgs {
                        op: op.clone(),
                        lhs_type: left_type_computed,
                        rhs_type: right_type_computed,
                        backtrace: Backtrace::capture(),
                    })
                    .wrap_span_annotations(*span, annotations);
                }

                Ok(output_type)
            }
            Expr::PrefixOp {
                op,
                operand,
                span,
                operand_type,
                op_span,
            } => {
                let operand_type_computed = match op {
                    PrefixOp::Cast(_) => {
                        // Preserve
                        operand.check_and_resolve_types(ctx)?
                    }
                    PrefixOp::Dereference
                    | PrefixOp::AddressOf
                    | PrefixOp::Negate
                    | PrefixOp::Invert
                    | PrefixOp::LNot => {
                        // Eval arg in read only
                        let (result, _frame) = ctx.define_scope(
                            |ctx| operand.check_and_resolve_types(ctx),
                            FrameKind::Regular,
                            CaptureKind::Read,
                        );

                        result?
                    }
                };

                let operand_type_computed = operand_type_computed.resolve_once(ctx)?;
                *operand_type = DeferedType::ResolvedType(operand_type_computed.clone());

                let (valid_types, return_type) = match op {
                    PrefixOp::Negate | PrefixOp::Invert => {
                        (matches!(operand_type_computed, Type::Int), Type::Int)
                    }
                    PrefixOp::LNot => (matches!(operand_type_computed, Type::Bool), Type::Bool),
                    PrefixOp::Cast(to) => {
                        if operand_type_computed.width(ctx)? == to.width(ctx)? {
                            (true, to.clone())
                        } else {
                            let annotations = vec![
                                (*op_span, format!("has the type `{operand_type_computed:?}`, but the cast target type {to:?} is a different width").into()),
                            ];

                            return Err(TypeError::CastWrongWidth {
                                src_type: operand_type_computed,
                                dst_type: to.clone(),
                                backtrace: Backtrace::capture(),
                            })
                            .wrap_span_annotations(*span, annotations);
                        }
                    }
                    PrefixOp::Dereference => {
                        if let Type::Pointer(target) = operand_type_computed.clone() {
                            (true, *target)
                        } else {
                            let annotations = vec![
                                (*op_span, format!("has the type `{operand_type_computed:?}`, which is not a pointer type").into()),
                            ];

                            return Err(TypeError::DereferenceNonPointer {
                                operand_type: operand_type_computed,
                                backtrace: Backtrace::capture(),
                            })
                            .wrap_span_annotations(*span, annotations);
                        }
                    }
                    PrefixOp::AddressOf => {
                        (true, Type::Pointer(operand_type_computed.clone().into()))
                    }
                };

                if !valid_types {
                    let annotations = vec![(
                        *op_span,
                        format!("has the type `{operand_type_computed:?}`, which is not permitted")
                            .into(),
                    )];

                    return Err(TypeError::PrefixOpBadArgs {
                        op: op.clone(),
                        operand_type: operand_type_computed,
                        backtrace: Backtrace::capture(),
                    })
                    .wrap_span_annotations(*span, annotations);
                }

                Ok(return_type)
            }
            Expr::PostfixOp {
                op,
                operand,
                span,
                operand_type,
                op_span,
            } => {
                let operand_type_computed = match op {
                    PostfixOp::Member(_) => {
                        // Preserve
                        operand.check_and_resolve_types(ctx)?
                    }
                    PostfixOp::MemberDeref(_) => {
                        // Eval arg in read only
                        let (result, _frame) = ctx.define_scope(
                            |ctx| operand.check_and_resolve_types(ctx),
                            FrameKind::Regular,
                            CaptureKind::Read,
                        );

                        result?
                    }
                    PostfixOp::ArrayIndex(_) => {
                        // Depends on operand_type
                        // - If operand is a pointer type then eval arg in read only
                        // - If operand is an array type then preserve

                        let (result_phantom, _frame) = ctx.define_scope(
                            |ctx| operand.check_and_resolve_types(ctx),
                            FrameKind::Phantom,
                            CaptureKind::Read,
                        );

                        match result_phantom?.resolve_once(ctx)? {
                            Type::Pointer(_) => {
                                // Eval arg in read only
                                let (result, _frame) = ctx.define_scope(
                                    |ctx| operand.check_and_resolve_types(ctx),
                                    FrameKind::Regular,
                                    CaptureKind::Read,
                                );

                                result?
                            }
                            Type::Array(_, _) => {
                                // Preserve
                                operand.check_and_resolve_types(ctx)?
                            }
                            _ => unreachable!(),
                        }
                    }
                };

                let operand_type_computed = operand_type_computed.resolve_once(ctx)?;
                *operand_type = DeferedType::ResolvedType(operand_type_computed.clone());

                let (valid_types, return_type) = match (&operand_type_computed, &mut *op) {
                    (
                        struct_type @ (Type::Struct(_) | Type::NamedTuple(_)),
                        PostfixOp::Member(ident),
                    ) => {
                        let member_type = struct_type
                            .member(ctx, ident)
                            .wrap_span_annotations(*span, vec![(*op_span, "here".into())])?;
                        (true, member_type)
                    }
                    (Type::Pointer(inner_type), PostfixOp::MemberDeref(ident)) => {
                        match inner_type.resolve_once(ctx)? {
                            struct_type @ (Type::Struct(_) | Type::NamedTuple(_)) => {
                                let member_type =
                                    struct_type.member(ctx, ident).wrap_span_annotations(
                                        *span,
                                        vec![(*op_span, "here".into())],
                                    )?;
                                (true, member_type)
                            }
                            _ => (false, Type::Void),
                        }
                    }
                    (
                        Type::Array(inner_type, _) | Type::Pointer(inner_type),
                        PostfixOp::ArrayIndex(expr),
                    ) => {
                        // Eval idx in read only
                        let (idx_result, _frame) = ctx.define_scope(
                            |ctx| expr.check_and_resolve_types(ctx),
                            FrameKind::Regular,
                            CaptureKind::Read,
                        );

                        let index_type = idx_result?.resolve_once(ctx)?;
                        let Type::Int = index_type else {
                            return Err(TypeError::BadArrayIndexType {
                                op: op.clone(),
                                index_type,
                                backtrace: Backtrace::capture(),
                            })
                            .wrap_span_annotations(*span, vec![(*op_span, "here".into())]);
                        };

                        (true, (**inner_type).clone())
                    }
                    _ => (false, Type::Void),
                };

                if !valid_types {
                    let annotations = vec![(
                        *op_span,
                        format!("has the type `{operand_type_computed:?}`, which is not permitted")
                            .into(),
                    )];

                    return Err(TypeError::PostfixOpBadArgs {
                        op: op.clone(),
                        operand_type: operand_type_computed,
                        backtrace: Backtrace::capture(),
                    })
                    .wrap_span_annotations(*span, annotations);
                }

                Ok(return_type)
            }
            Expr::FunctionCall(func_call) => {
                // Eval function call in read only
                let (result, _frame) = ctx.define_scope(
                    |ctx| func_call.check_and_resolve_types(ctx),
                    FrameKind::Regular,
                    CaptureKind::Read,
                );

                result
            }
            Expr::If(if_expr) => {
                // Eval function call in read only
                let (result, _frame) = ctx.define_scope(
                    |ctx| if_expr.check_and_resolve_types(ctx),
                    FrameKind::Regular,
                    CaptureKind::Read,
                );

                result
            }
            Expr::Box(expr, defered_type, _span) => {
                // Eval box arg in read only
                let (result, _frame) = ctx.define_scope(
                    |ctx| expr.check_and_resolve_types(ctx),
                    FrameKind::Regular,
                    CaptureKind::Read,
                );

                let result = result?;
                *defered_type = DeferedType::ResolvedType(result.clone());

                Ok(Type::Pointer(result.into()))
            }
            Expr::Block(block) => {
                // Eval block in read only
                let (result, _frame) = ctx.define_scope(
                    |ctx| block.check_and_resolve_types(ctx),
                    FrameKind::Regular,
                    CaptureKind::Read,
                );

                result
            }
        }
    }
}

impl<'a> TypeCheck<'a> for FunctionCall<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let (sig, _span) = ctx.lookup_function(self.function).wrap_span(self.span)?;
        let sig = sig.clone();

        if self.parameters.len() != sig.arguements.len() {
            return Err(TypeError::FunctionCallArgCount {
                function: self.clone(),
                signature: sig,
                backtrace: Backtrace::capture(),
            })
            .wrap_span(self.span);
        }

        for (parm_expr, arguement) in self.parameters.iter_mut().zip(sig.arguements.iter()) {
            let Arguement {
                arg_type,
                arg_name,
                version: _,
                span: _,
            } = arguement;

            let parm_type = parm_expr.check_and_resolve_types(ctx)?;
            let arg_type = arg_type;
            if !parm_type.compatible_with(arg_type, ctx)? {
                let annotations = vec![(parm_expr.as_span(), "here".into())];

                return Err(TypeError::FunctionCallArgBadType {
                    arg_expr: parm_expr.clone(),
                    function: self.clone(),
                    signature: sig.clone(),
                    parm_name: *arg_name,
                    expected_type: arg_type.clone(),
                    provided_type: parm_type,
                    backtrace: Backtrace::capture(),
                })
                .wrap_span_annotations(self.span, annotations);
            }
        }

        // On the first pass, captures will not be available
        // But on the second pass, they will be and need to be propagated
        if let DeferedCaptures::ResolvedCaptures(_) = sig.captures {
            for (_, _, version, kind, _) in sig.captures_read()? {
                ctx.lookup_variable_versioned(version, kind)?;
            }
        }

        Ok(sig.return_type.clone())
    }
}

impl<'a> TypeCheck<'a> for FunctionDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let kind = if self.attributes.contains(&FunctionAttribute::LangItem) {
            FunctionKind::LangItem
        } else {
            FunctionKind::Regular
        };

        let (actual_return_type, frame) =
            ctx.define_function(self.function, &mut self.signature, self.span, kind, |ctx| {
                self.contents.check_and_resolve_types(ctx)
            });

        if self.attributes.contains(&FunctionAttribute::NoCaptures) {
            let captures = frame.get_captures();
            if !captures.0.is_empty() {
                return Err(TypeError::IllegalCaptures {
                    function: self.clone(),
                    captures,
                    backtrace: Backtrace::capture(),
                });
            }
        }

        let actual_return_type = actual_return_type?;

        if !actual_return_type.compatible_with(&self.signature.return_type, ctx)? {
            let last_statement = self.contents.statements.last();
            let last_statement_span = last_statement
                .as_ref()
                .map(|it| it.as_span())
                .unwrap_or_else(|| self.contents.as_span());

            let annotations = vec![(
                last_statement_span,
                format!("This returns {actual_return_type}").into(),
            )];

            return Err(TypeError::BlockReturnsWrongType {
                block: self.contents.clone(),
                expected_return_type: self.signature.return_type.clone(),
                actual_return_type,
                last_statement: self.contents.statements.last().cloned(),
                backtrace: Backtrace::capture(),
            })
            .wrap_span_annotations(self.span, annotations);
        }

        // Computing captures got moved into ctx.define_function

        // The Function Definition it self should not have a rrtuen type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for ConstDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let mut actual_type = self.expr.check_and_resolve_types(ctx)?;

        match &mut self.var_type {
            DeferedType::ResolvedType(expected_type) => {
                if !actual_type.compatible_with(expected_type, ctx)? {
                    let annotations = vec![(
                        self.expr.as_span(),
                        format!(
                            "has the type `{actual_type}`, but a `{expected_type}` is required"
                        )
                        .into(),
                    )];

                    return Err(TypeError::ConstDefTypeMismatch {
                        expected_type: expected_type.clone(),
                        provided_type: actual_type.clone(),
                        constant: self.clone(),
                        backtrace: Backtrace::capture(),
                    })
                    .wrap_span_annotations(self.span, annotations);
                } else {
                    actual_type = expected_type.clone();
                }
            }
            DeferedType::UnresolvedType => {
                self.var_type = DeferedType::ResolvedType(actual_type.clone());
            }
        }

        // Variable needs to be defined after we type check its expression so it cant be
        // recursively defined. (We arent trying to impl nix lol)
        let version =
            ctx.define_variable(self.name, actual_type, VariableKind::Constant, self.span);
        self.version = DeferedVersion::ResolvedVersion(version);

        // The const definition it self should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for LocalDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let mut actual_type = self.expr.check_and_resolve_types(ctx)?;

        match &mut self.var_type {
            DeferedType::ResolvedType(expected_type) => {
                if !actual_type.compatible_with(expected_type, ctx)? {
                    let annotations = vec![(
                        self.expr.as_span(),
                        format!(
                            "has the type `{actual_type}`, but a `{expected_type}` is required"
                        )
                        .into(),
                    )];

                    return Err(TypeError::LocalDefTypeMismatch {
                        expected_type: expected_type.clone(),
                        provided_type: actual_type,
                        local: self.clone(),
                        backtrace: Backtrace::capture(),
                    })
                    .wrap_span_annotations(self.span, annotations);
                } else {
                    actual_type = expected_type.clone();
                }
            }
            DeferedType::UnresolvedType => {
                self.var_type = DeferedType::ResolvedType(actual_type.clone());
            }
        }

        // Variable needs to be defined after we type check its expression so it cant be
        // recursively defined. (We arent trying to impl nix lol)
        let version = ctx.define_variable(self.name, actual_type, VariableKind::Local, self.span);
        self.version = DeferedVersion::ResolvedVersion(version);

        // The Local Definition it self should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for Assignment<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        // Eval target call in read write
        let (target_type, _frame) = ctx.define_scope(
            |ctx| self.target.check_and_resolve_types(ctx),
            FrameKind::Regular,
            CaptureKind::ReadWrite,
        );

        let expr_type = self.expr.check_and_resolve_types(ctx)?.resolve_once(ctx)?;
        let target_type = target_type?.resolve_once(ctx)?;

        let mismatched_type = match (&target_type, &expr_type) {
            (target_type, Type::Array(array_type, _len))
                if !target_type.compatible_with(&expr_type, ctx)? =>
            {
                !target_type.compatible_with(array_type, ctx)?
            }
            (target_type, expr_type) => !target_type.compatible_with(expr_type, ctx)?,
        };

        if mismatched_type {
            let annotations = vec![(
                self.expr.as_span(),
                format!(
                    "the type `{}`\n, can not be assigned to a place of type a `{}`",
                    expr_type, target_type
                )
                .into(),
            )];

            return Err(TypeError::AssignmentTypeMismatch {
                assignment: self.clone(),
                target_type,
                expr_type,
                backtrace: Backtrace::capture(),
            })
            .wrap_span_annotations(self.span, annotations);
        }

        self.expr_type = DeferedType::ResolvedType(expr_type);
        self.target_type = DeferedType::ResolvedType(target_type);

        // The pointer assignment itself should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for Loop<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let (frame, _outer_frame) = ctx.define_scope(
            |ctx| -> Result<_> {
                if let Some(init) = &mut self.init {
                    init.check_and_resolve_types(ctx)?;
                }

                let (result, frame) = ctx.define_scope(
                    |ctx| -> Result<_> {
                        if let Some(cond) = &mut self.cond {
                            let case_type = cond.check_and_resolve_types(ctx)?.resolve_once(ctx)?;

                            if !matches!(case_type, Type::Bool) {
                                let annotations = vec![(
                                    cond.as_span(),
                                    format!(
                                        "has the type `{case_type}`, but a `{}` is required",
                                        Type::Bool
                                    )
                                    .into(),
                                )];

                                return Err(TypeError::ConditionIsntBool {
                                    condition: cond.clone(),
                                    expr_type: case_type,
                                    backtrace: Backtrace::capture(),
                                })
                                .wrap_span_annotations(self.span, annotations);
                            }
                        }

                        if let Some(update) = &mut self.update {
                            update.check_and_resolve_types(ctx)?;
                        }

                        self.body.check_and_resolve_types(ctx)?;

                        Ok(())
                    },
                    FrameKind::Regular,
                    CaptureKind::Read,
                );

                result.map(|_| frame)
            },
            FrameKind::Regular,
            CaptureKind::Read,
        );

        self.captures = DeferedCaptures::ResolvedCaptures(frame?.get_captures());

        // A loop does not produce a value
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for Typedef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        ctx.define_type(self.name, self.type_alias.clone(), self.span)?;

        // A typedef does not produce a value
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for IfCase<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let case_type = self
            .condition
            .check_and_resolve_types(ctx)?
            .resolve_once(ctx)?;
        if !matches!(case_type, Type::Bool) {
            let annotations = vec![(
                self.condition.as_span(),
                format!(
                    "has the type `{case_type}`, but a `{}` is required",
                    Type::Bool
                )
                .into(),
            )];

            return Err(TypeError::ConditionIsntBool {
                condition: self.condition.clone(),
                expr_type: case_type,
                backtrace: Backtrace::capture(),
            })
            .wrap_span_annotations(self.span, annotations);
        }

        self.contents.check_and_resolve_types(ctx)
    }
}

impl<'a> TypeCheck<'a> for IfExpr<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let expected_type = self
            .cases
            .first_mut()
            .unwrap()
            .check_and_resolve_types(ctx)?;

        let (rst, frame) = ctx.define_scope(
            |ctx| -> Result<_> {
                for case in &mut self.cases {
                    let actual_return_type = case.check_and_resolve_types(ctx)?;
                    if !actual_return_type.compatible_with(&expected_type, ctx)? {
                        let last_statement = case.contents.statements.last();
                        let last_statement_span = last_statement
                            .as_ref()
                            .map(|it| it.as_span())
                            .unwrap_or_else(|| case.contents.as_span());

                        let annotations = vec![(
                            last_statement_span,
                            format!("This returns {actual_return_type}").into(),
                        )];

                        return Err(TypeError::BlockReturnsWrongType {
                            block: case.contents.clone(),
                            actual_return_type,
                            expected_return_type: expected_type.clone(),
                            last_statement: case.contents.statements.last().cloned(),
                            backtrace: Backtrace::capture(),
                        })
                        .wrap_span_annotations(self.span, annotations);
                    }
                }

                if let Some(otherwise) = &mut self.otherwise {
                    let actual_return_type = otherwise.check_and_resolve_types(ctx)?;
                    if !actual_return_type.compatible_with(&expected_type, ctx)? {
                        let last_statement = otherwise.statements.last();
                        let last_statement_span = last_statement
                            .as_ref()
                            .map(|it| it.as_span())
                            .unwrap_or_else(|| otherwise.as_span());

                        let annotations = vec![(
                            last_statement_span,
                            format!("This returns {actual_return_type}").into(),
                        )];

                        return Err(TypeError::BlockReturnsWrongType {
                            block: otherwise.clone(),
                            actual_return_type,
                            expected_return_type: expected_type.clone(),
                            last_statement: otherwise.statements.last().cloned(),
                            backtrace: Backtrace::capture(),
                        })
                        .wrap_span_annotations(self.span, annotations);
                    }
                }

                Ok(())
            },
            FrameKind::Regular,
            CaptureKind::Read,
        );

        self.return_type = DeferedType::ResolvedType(expected_type.clone());
        self.captures = DeferedCaptures::ResolvedCaptures(frame.get_captures());

        rst.map(|_| expected_type)
    }
}

impl<'a> TypeCheck<'a> for Statement<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        match self {
            Statement::FunctionDef(function_def) => function_def.check_and_resolve_types(ctx),
            Statement::Const(const_def) => const_def.check_and_resolve_types(ctx),
            Statement::Local(local_def) => local_def.check_and_resolve_types(ctx),
            Statement::Expr(expr, Punctuation::Unpunctuated) => expr.check_and_resolve_types(ctx),
            Statement::Expr(expr, Punctuation::Punctuated) => {
                expr.check_and_resolve_types(ctx)?;
                Ok(Type::Void)
            }
            Statement::Assignment(ptr_assign) => ptr_assign.check_and_resolve_types(ctx),
            Statement::Typedef(typedef) => typedef.check_and_resolve_types(ctx),
            Statement::Defer(block) => {
                block.check_and_resolve_types(ctx)?;
                Ok(Type::Void)
            }
            Statement::Loop(inner) => {
                inner.check_and_resolve_types(ctx)?;
                Ok(Type::Void)
            }
        }
    }
}

impl<'a> TypeCheck<'a> for Block<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<'a, Type<'a>> {
        ctx.check_break_point(self)?;

        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let mut actual_return_type = Type::Void;

        let (res, frame) = ctx.define_scope(
            |ctx| -> Result<_> {
                for statement in &mut self.statements {
                    actual_return_type = statement.check_and_resolve_types(ctx)?;
                }

                Ok(())
            },
            FrameKind::Regular,
            CaptureKind::Read,
        );

        self.captures = DeferedCaptures::ResolvedCaptures(frame.get_captures());

        res.map(|()| actual_return_type)
    }
}
