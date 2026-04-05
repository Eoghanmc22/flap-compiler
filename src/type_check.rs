use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::{self, Debug, Display},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Result, eyre},
};
use pest::Span;

use crate::{
    ast::{
        AsSpan, Assignment, BinaryOp, Block, CaptureKind, Captures, ConstDef, DeferedCaptures,
        DeferedType, DeferedVersion, Expr, FunctionCall, FunctionDef, FunctionSignature, IdentRef,
        IfCase, IfExpr, LocalDef, Loop, PostfixOp, PrefixOp, Punctuation, Statement, Type, Typedef,
        Value, VariableVersion,
    },
    codegen::{builtins::clac_builtins, clac::ClacValue},
    middleware::{generate_span_error_section, generate_span_error_section_with_annotations},
};

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

#[derive(Debug, Clone)]
pub struct TypeCheckerFrame<'a> {
    pub variables: HashMap<IdentRef<'a>, VariableVersion>,
    pub variables_versioned: HashMap<VariableVersion, (IdentRef<'a>, Type<'a>, VariableKind)>,
    pub functions: HashMap<IdentRef<'a>, FunctionSignature<'a>>,

    pub frame_kind: FrameKind,
    pub capture_kind: CaptureKind,
}

impl<'a> TypeCheckerFrame<'a> {
    pub fn get_captures(&self) -> Captures<'a> {
        Captures(
            self.variables_versioned
                .iter()
                .filter_map(|(version, (ident, data_type, kind))| match kind {
                    VariableKind::Capture(capture_kind) => {
                        Some((*version, (data_type.clone(), *ident, *capture_kind)))
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
    pub typedefs: HashMap<IdentRef<'a>, Type<'a>>,
    version_counter: Arc<AtomicU64>,
}

impl Display for TypeChecker<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeChecker {{ scope: [ ")?;

        let mut already_printed = HashSet::new();
        for frame in self.scope_stack.iter().rev() {
            for (version, (ident, data_type, kind)) in &frame.variables_versioned {
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
            version_counter: Arc::default(),
        };

        for (ident, (_code, mut sig)) in clac_builtins() {
            type_checker.define_function(ident, &mut sig, |_| {});
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
        mut scope: F,
    ) -> (T, TypeCheckerFrame<'a>) {
        self.top_scope_frame()
            .functions
            .insert(ident, signature.clone());

        self.define_scope(
            |ctx| {
                for (var_type, ident, defered_version) in &mut signature.arguements {
                    let version = ctx.define_variable(ident, var_type.clone(), VariableKind::Local);
                    *defered_version = DeferedVersion::ResolvedVersion(version);
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
                    .insert(ident, signature.clone());
                (scope)(ctx)
            },
            FrameKind::Regular,
            CaptureKind::Read,
        )
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

    pub fn define_variable(
        &mut self,
        ident: IdentRef<'a>,
        var_type: Type<'a>,
        kind: VariableKind,
    ) -> VariableVersion {
        let version = self.allocate_version();

        let frame = self.top_scope_frame();
        frame.variables.insert(ident, version);
        frame
            .variables_versioned
            .insert(version, (ident, var_type, kind));

        version
    }

    pub fn define_type(&mut self, ident: IdentRef<'a>, type_alias: Type<'a>) -> Result<()> {
        let res = self.typedefs.insert(ident, type_alias);

        match res {
            Some(_) => Err(eyre!("Type `{ident}` is defined multiple times")),
            None => Ok(()),
        }
    }

    pub fn frame_kind(&mut self) -> FrameKind {
        self.top_scope_frame().frame_kind
    }

    pub fn capture_kind(&mut self) -> CaptureKind {
        self.top_scope_frame().capture_kind
    }

    pub fn lookup_function(&mut self, ident: IdentRef<'a>) -> Option<&FunctionSignature<'a>> {
        for frame in self.scope_stack.iter().rev() {
            if let Some(sig) = frame.functions.get(&ident) {
                return Some(sig);
            }
        }

        None
    }

    // TODO: need a way to repersent scopes where captures are not taken such as arguements to
    // sizeof() expressions
    pub fn lookup_variable_versioned(
        &mut self,
        var: VariableVersion,
        capture_kind: CaptureKind,
    ) -> Result<(Type<'a>, VariableVersion)> {
        let frame_kind = self.frame_kind();

        for (idx, frame) in self.scope_stack.iter().rev().enumerate() {
            if let Some((ident, var_type, kind @ (VariableKind::Local | VariableKind::Constant))) =
                frame.variables_versioned.get(&var)
            {
                let ident = *ident;
                let var_type = var_type.clone();

                if let FrameKind::Regular = frame_kind
                    && let VariableKind::Local = kind
                {
                    for frame in self.scope_stack.iter_mut().rev().take(idx) {
                        let (_, _, VariableKind::Capture(prev_mode)) =
                            frame.variables_versioned.entry(var).or_insert((
                                ident,
                                var_type.clone(),
                                VariableKind::Capture(capture_kind),
                            ))
                        else {
                            unreachable!()
                        };

                        *prev_mode = (*prev_mode).max(capture_kind)
                    }
                }

                return Ok((var_type, var));
            }
        }

        Err(eyre!("Variable {var} is not in scope"))
    }

    // TODO: need a way to repersent scopes where captures are not taken such as arguements to
    // sizeof() expressions
    pub fn lookup_variable(&mut self, var: IdentRef<'a>) -> Result<(Type<'a>, VariableVersion)> {
        let capture_kind = self.capture_kind();

        for frame in self.scope_stack.iter().rev() {
            if let Some(version) = frame.variables.get(var) {
                return self.lookup_variable_versioned(*version, capture_kind);
            }
        }

        Err(eyre!("Variable {var} is not in scope"))
    }
}

pub trait TypeCheck<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>>;
}

impl<'a> TypeCheck<'a> for Value<'a> {
    fn check_and_resolve_types(&mut self, _ctx: &mut TypeChecker) -> Result<Type<'a>> {
        Ok(self.compute_type())
    }
}

impl<'a> TypeCheck<'a> for Expr<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
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
            Expr::Value(value, span) => value
                .check_and_resolve_types(ctx)
                .wrap_err("Could not type check expr value")
                .with_section(|| generate_span_error_section(*span)),
            Expr::Variable(ident, defered_version, span) => {
                let (var_type, version) = ctx
                    .lookup_variable(ident)
                    .wrap_err_with(|| format!("Could not find identifier: `{ident:?}`"))
                    .with_section(|| generate_span_error_section(*span))?;

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
            Expr::Array(exprs, defered_type, span) => {
                let types = exprs
                    .into_iter()
                    .map(|expr| Ok((expr.as_span(), expr.check_and_resolve_types(ctx)?)))
                    .collect::<Result<Vec<_>>>()?;

                let mut inner_type: Option<(Span, &Type)> = None;
                for (span, expr_type) in &types {
                    if let Some((first, inner_type)) = inner_type {
                        if !inner_type.compatible_with(expr_type, ctx)? {
                            return Err(eyre!("All array elements must be of the same type")
                                .with_section(|| {
                                    generate_span_error_section_with_annotations(
                                        *span,
                                        &[
                                            (first, &format!("has the type `{inner_type:?}`")),
                                            (*span, &format!("has differing type `{expr_type:?}`")),
                                        ],
                                    )
                                }));
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
                    return Err(eyre!(
                        "Empty arrays are not supported due to type resolution limitations"
                    )
                    .with_section(|| generate_span_error_section(*span)));
                }
            }
            Expr::BinaryOp {
                op,
                left,
                right,
                span,
                left_type,
                right_type,
            } => {
                assert_eq!(ctx.capture_kind(), CaptureKind::Read);

                let left_type_computed = left.check_and_resolve_types(ctx)?.resolve_once(ctx)?;
                let right_type_computed = right.check_and_resolve_types(ctx)?.resolve_once(ctx)?;

                *left_type = DeferedType::ResolvedType(left_type_computed.clone());
                *right_type = DeferedType::ResolvedType(right_type_computed.clone());

                if left_type_computed.width(ctx)? != 1 || right_type_computed.width(ctx)? != 1 {
                    return Err(eyre!("Binary op {op} only support types that are 1 word")
                        .with_section(|| generate_span_error_section(*span)));
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
                            | BinaryOp::BAnd,
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
                    return Err(eyre!("Binary op {op} uses a disallowed type").with_section(|| {
                        generate_span_error_section_with_annotations(
                            *span,
                            &[(
                                *span,
                                &format!(
                                    "lhs has the type `{left_type_computed:?}` and rhs has the type `{right_type_computed:?}`, which is not permitted"
                                ),
                            )],
                        )
                    }));
                }

                Ok(output_type)
            }
            Expr::PrefixOp {
                op,
                operand,
                span,
                operand_type,
            } => {
                let operand_type_computed = match op {
                    PrefixOp::Cast(_) => {
                        // Preserve
                        operand.check_and_resolve_types(ctx)?
                    }
                    PrefixOp::Dereference => {
                        // Eval arg in read only
                        let (result, _frame) = ctx.define_scope(
                            |ctx| operand.check_and_resolve_types(ctx),
                            FrameKind::Regular,
                            CaptureKind::Read,
                        );

                        result?
                    }
                    PrefixOp::AddressOf | PrefixOp::Negate | PrefixOp::LNot => {
                        // Should be read only
                        assert_eq!(ctx.capture_kind(), CaptureKind::Read);
                        operand.check_and_resolve_types(ctx)?
                    }
                };

                let operand_type_computed = operand_type_computed.resolve_once(ctx)?;
                *operand_type = DeferedType::ResolvedType(operand_type_computed.clone());

                let (valid_types, return_type) = match op {
                    PrefixOp::Negate => (matches!(operand_type_computed, Type::Int), Type::Int),
                    PrefixOp::LNot => (matches!(operand_type_computed, Type::Bool), Type::Bool),
                    PrefixOp::Cast(to) => {
                        if operand_type_computed.width(ctx)? == to.width(ctx)? {
                            (true, to.clone())
                        } else {
                            return Err(eyre!("Can not cast between types of differing width")
                        .with_section(|| {
                            generate_span_error_section_with_annotations(
                                *span,
                                &[
                                    (*span, &format!("has the type `{operand_type_computed:?}`, but the cast target type {to:?} is a different width")),
                                ],
                            )
                        }));
                        }
                    }
                    PrefixOp::Dereference => {
                        if let Type::Pointer(target) = operand_type_computed.clone() {
                            (true, *target)
                        } else {
                            return Err(eyre!("Can not dereference a non pointer type")
                                .with_section(|| {
                                    generate_span_error_section_with_annotations(
                                        *span,
                                        &[
                                            (*span, &format!("has the type `{operand_type_computed:?}`, which is not a pointer type")),
                                        ],
                                    )
                                }));
                        }
                    }
                    PrefixOp::AddressOf => {
                        (true, Type::Pointer(operand_type_computed.clone().into()))
                    }
                };

                if !valid_types {
                    return Err(eyre!("Prefix op uses a disallowed type")
                        .with_section(|| {
                            generate_span_error_section_with_annotations(
                                *span,
                                &[
                                    (*span, &format!("has the type `{operand_type_computed:?}`, which is not permitted")),
                                ],
                            )
                        }));
                }

                Ok(return_type)
            }
            Expr::PostfixOp {
                op,
                operand,
                span,
                operand_type,
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
                    (Type::Struct(map), PostfixOp::Member(ident)) => {
                        if let Some(val_type) = map.get(ident) {
                            (true, val_type.clone())
                        } else {
                            return Err(eyre!("Attempting to access non-existant field {ident} on struct {operand_type_computed}")
                                .with_section(|| {
                                    generate_span_error_section(
                                        *span,
                                    )
                                }));
                        }
                    }
                    (Type::Pointer(inner_type), PostfixOp::MemberDeref(ident)) => {
                        match inner_type.resolve_once(ctx)? {
                            Type::Struct(map) => {
                                if let Some(val_type) = map.get(ident) {
                                    (true, val_type.clone())
                                } else {
                                    return Err(eyre!("Attempting to access non-existant field {ident} on struct {operand_type_computed} with arrow operator")
                                .with_section(|| {
                                    generate_span_error_section(
                                        *span,
                                    )
                                }));
                                }
                            }
                            _ => {
                                return Err(eyre!("Attempting to use arrow on a pointer to a non-struct type {inner_type}")
                                .with_section(|| {
                                    generate_span_error_section(
                                        *span,
                                    )
                                }));
                            }
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

                        let idx_type = idx_result?.resolve_once(ctx)?;
                        let Type::Int = idx_type else {
                            return Err(eyre!("Attempting to index into an array or pointer with a expression of non Int type: {idx_type}")
                                .with_section(|| {
                                    generate_span_error_section_with_annotations(
                                        *span,
                                        &[
                                            (expr.as_span(), "here")
                                        ]
                                    )
                                }));
                        };

                        (true, (**inner_type).clone())
                    }
                    _ => (false, Type::Void),
                };

                if !valid_types {
                    return Err(eyre!("Postfix op {op} a disallowed type {operand_type_computed}")
                        .with_section(|| {
                            generate_span_error_section_with_annotations(
                                *span,
                                &[
                                    (*span, &format!("has the type `{operand_type_computed:?}`, which is not permitted")),
                                ],
                            )
                        }));
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
        }
    }
}

impl<'a> TypeCheck<'a> for FunctionCall<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let sig = ctx
            .lookup_function(self.function)
            .wrap_err_with(|| format!("Could not find function: {}", self.function))
            .with_section(|| generate_span_error_section(self.span))?
            .clone();

        if self.parameters.len() != sig.arguements.len() {
            return Err(eyre!("Function called with the incorrect number of arguements")
                        .with_section(|| {
                            generate_span_error_section_with_annotations(
                                self.span,
                                &[
                                    (self.span, &format!("The function `{}` was called with {} parameters but it was defined to have {} arguements.\nThe function was defined with the signature: {sig:?}", self.function, self.parameters.len(), sig.arguements.len())),
                                ],
                            )
                        }));
        }

        for (parm_expr, (arg_type, arg_name, _)) in
            self.parameters.iter_mut().zip(sig.arguements.iter())
        {
            let parm_type = parm_expr.check_and_resolve_types(ctx)?;
            let arg_type = arg_type;
            if !parm_type.compatible_with(arg_type, ctx)? {
                return Err(eyre!("Function called with a paramater of the incorrect type")
                            .with_section(|| {
                                generate_span_error_section_with_annotations(
                                    self.span,
                                    &[
                                        (parm_expr.as_span(), &format!("has the type `{parm_type:?}`, but the arguemment `{arg_name}` to the function `{}` expected the type `{arg_type:?}`", self.function)),
                                    ],
                                )
                            }));
            }
        }

        // On the first pass, captures will not be available
        // But on the second pass, they will be and need to be propagated
        if let DeferedCaptures::ResolvedCaptures(_) = sig.captures {
            for (_, _, version, kind) in sig.captures_read()? {
                ctx.lookup_variable_versioned(version, kind)?;
            }
        }

        Ok(sig.return_type.clone())
    }
}

impl<'a> TypeCheck<'a> for FunctionDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let (actual_return_type, _frame) =
            ctx.define_function(self.function, &mut self.signature, |ctx| {
                self.contents.check_and_resolve_types(ctx)
            });

        let actual_return_type = actual_return_type?;

        if !actual_return_type.compatible_with(&self.signature.return_type, ctx)? {
            return Err(eyre!("Function definition returns the incorrect type")
                .with_section(|| {
                    generate_span_error_section_with_annotations(
                        self.span,
                        &[(
                            self.contents
                                .statements
                                .last()
                                .map(|it| it.as_span())
                                .unwrap_or_else(|| self.contents.as_span())
                                .lines_span()
                                .last()
                                .unwrap_or_else(|| self.contents.as_span()),
                            &format!(
                                "has the type `{actual_return_type:?}`, but a `{:?}` is required",
                                self.signature.return_type
                            ),
                        )],
                    )
                })
                .with_section(|| {
                    format!("Last statement: {:#?}", self.contents.statements.last())
                }));
        }

        // Computing captures got moved into ctx.define_function

        // The Function Definition it self should not have a rrtuen type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for ConstDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let mut actual_type = self.expr.check_and_resolve_types(ctx)?;

        match &mut self.var_type {
            DeferedType::ResolvedType(expected_type) => {
                if !actual_type.compatible_with(expected_type, ctx)? {
                    return Err(
                        eyre!("Const definition set to the incorrect type").with_section(|| {
                            generate_span_error_section_with_annotations(
                                self.span,
                                &[(
                                    self.expr_span,
                                    &format!(
                                        "has the type `{actual_type:?}`, but a `{:?}` is required",
                                        expected_type
                                    ),
                                )],
                            )
                        }),
                    );
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
        let version = ctx.define_variable(self.name, actual_type, VariableKind::Constant);
        self.version = DeferedVersion::ResolvedVersion(version);

        // The const definition it self should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for LocalDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let mut actual_type = self.expr.check_and_resolve_types(ctx)?;

        match &mut self.var_type {
            DeferedType::ResolvedType(expected_type) => {
                if !actual_type.compatible_with(expected_type, ctx)? {
                    return Err(
                        eyre!("Local definition set to the incorrect type").with_section(|| {
                            generate_span_error_section_with_annotations(
                                self.span,
                                &[(
                                    self.expr.as_span(),
                                    &format!(
                                        "has the type `{actual_type:?}`, but a `{:?}` is required",
                                        expected_type
                                    ),
                                )],
                            )
                        }),
                    );
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
        let version = ctx.define_variable(self.name, actual_type, VariableKind::Local);
        self.version = DeferedVersion::ResolvedVersion(version);

        // The Local Definition it self should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for Assignment<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        // Eval target call in read write
        let (target_type, _frame) = ctx.define_scope(
            |ctx| self.target.check_and_resolve_types(ctx),
            FrameKind::Regular,
            CaptureKind::ReadWrite,
        );

        let expr_type = self.expr.check_and_resolve_types(ctx)?;
        let target_type = target_type?;

        let mismatched_type = match (&target_type, &expr_type) {
            (target_type, Type::Array(array_type, _len))
                if !target_type.compatible_with(&expr_type, ctx)? =>
            {
                !target_type.compatible_with(array_type, ctx)?
            }
            (target_type, expr_type) => !target_type.compatible_with(expr_type, ctx)?,
        };

        if mismatched_type {
            return Err(eyre!("Assignment mismatching types").with_section(|| {
                generate_span_error_section_with_annotations(
                    self.span,
                    &[(
                        self.expr.as_span(),
                        &format!(
                            "the type `{:?}`\n, can not be assigned to a place of type a `{:?}`",
                            expr_type.resolve_once(ctx),
                            target_type.resolve_once(ctx)
                        ),
                    )],
                )
            }));
        }

        self.expr_type = DeferedType::ResolvedType(expr_type);
        self.target_type = DeferedType::ResolvedType(target_type);

        // The pointer assignment itself should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for Loop<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
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
                                return Err(eyre!("Loop's condition evaluated to the incorrect type")
                        .with_section(|| {
                            generate_span_error_section_with_annotations(
                                self.span,
                                &[(
                                    cond.as_span(),
                                    &format!(
                                        "has the type `{case_type:?}`, but a `{:?}` is required",
                                        Type::Bool
                                    ),
                                )],
                            )
                        }));
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
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        ctx.define_type(self.name, self.type_alias.clone())?;

        // A typedef does not produce a value
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for IfCase<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let case_type = self
            .condition
            .check_and_resolve_types(ctx)?
            .resolve_once(ctx)?;
        if !matches!(case_type, Type::Bool) {
            return Err(
                eyre!("If statement's condition evaluated to the incorrect type").with_section(
                    || {
                        generate_span_error_section_with_annotations(
                            self.span,
                            &[(
                                self.condition.as_span(),
                                &format!(
                                    "has the type `{case_type:?}`, but a `{:?}` is required",
                                    Type::Bool
                                ),
                            )],
                        )
                    },
                ),
            );
        }

        self.contents.check_and_resolve_types(ctx)
    }
}

impl<'a> TypeCheck<'a> for IfExpr<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        assert_eq!(ctx.capture_kind(), CaptureKind::Read);

        let expected_type = self
            .cases
            .first_mut()
            .unwrap()
            .check_and_resolve_types(ctx)?;

        let (rst, frame) = ctx.define_scope(
            |ctx| -> Result<_> {
                for case in &mut self.cases {
                    let case_return_type = case.check_and_resolve_types(ctx)?;
                    if !case_return_type.compatible_with(&expected_type, ctx)? {
                        return Err(
                    eyre!("If case's block evaluated to the incorrect type").with_section(|| {
                        generate_span_error_section_with_annotations(
                            case.span,
                            &[(
                                case.contents
                                    .statements
                                    .last()
                                    .map(|it| it.as_span())
                                    .unwrap_or_else(|| case.contents.as_span()),
                                &format!(
                                    "has the type `{case_return_type:?}`, but a `{:?}` is required",
                                    expected_type
                                ),
                            )],
                        )
                    }),
                );
                    }
                }

                if let Some(otherwise) = &mut self.otherwise {
                    let case_return_type = otherwise.check_and_resolve_types(ctx)?;
                    if !case_return_type.compatible_with(&expected_type, ctx)? {
                        return Err(
                    eyre!("If case's block evaluated to the incorrect type").with_section(|| {
                        generate_span_error_section_with_annotations(
                            otherwise.as_span(),
                            &[(
                                otherwise
                                    .statements
                                    .last()
                                    .map(|it| it.as_span())
                                    .unwrap_or_else(|| otherwise.as_span()),
                                &format!(
                                    "has the type `{case_return_type:?}`, but a `{:?}` is required",
                                    expected_type
                                ),
                            )],
                        )
                    }),
                );
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
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
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
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
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
