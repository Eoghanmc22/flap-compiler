use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::{self, Debug, Display},
    sync::Arc,
};

use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Result, eyre},
};
use pest::Span;

use crate::{
    ast::{
        AsSpan, Assignment, BinaryOp, Block, Captures, ConstDef, DeferedCaptures, DeferedType,
        Expr, FunctionCall, FunctionDef, FunctionSignature, IdentRef, IfCase, IfExpr, LocalDef,
        PostfixOp, PrefixOp, Punctuation, Statement, Type, Typedef, Value,
    },
    codegen::{builtins::clac_builtins, clac::ClacValue},
    middleware::{generate_span_error_section, generate_span_error_section_with_annotations},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariableKind {
    Local,
    Constant,
    Capture,
}

#[derive(Debug, Clone, Default)]
pub struct TypeCheckerFrame<'a> {
    pub variables: HashMap<IdentRef<'a>, (Type<'a>, VariableKind)>,
    pub functions: HashMap<IdentRef<'a>, Arc<FunctionSignature<'a>>>,
}

impl<'a> TypeCheckerFrame<'a> {
    pub fn get_captures(&self) -> Captures<'a> {
        Captures {
            captures: self
                .variables
                .iter()
                .filter(|(_, (_, kind))| *kind == VariableKind::Capture)
                .map(|(ident, (data_type, _))| (*ident, data_type.clone()))
                .collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeChecker<'a> {
    pub scope_stack: Vec<TypeCheckerFrame<'a>>,
    pub typedefs: HashMap<IdentRef<'a>, Type<'a>>,
}

impl Display for TypeChecker<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeChecker {{ scope: [ ")?;

        let mut already_printed = HashSet::new();
        for frame in self.scope_stack.iter().rev() {
            for (ident, (data_type, kind)) in &frame.variables {
                if already_printed.insert(ident) {
                    write!(f, "{} {} ({:?}); ", data_type, ident, kind)?;
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
        };

        for (ident, (_code, sig)) in clac_builtins() {
            type_checker.define_function(ident, sig, |_| {});
        }

        type_checker.push_scope_frame();

        type_checker
    }
}

impl<'a> TypeChecker<'a> {
    fn push_scope_frame(&mut self) -> &mut TypeCheckerFrame<'a> {
        self.scope_stack.push_mut(TypeCheckerFrame {
            variables: Default::default(),
            functions: Default::default(),
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
            self.push_scope_frame()
        } else {
            self.scope_stack.last_mut().unwrap()
        }
    }

    pub fn define_function<T, F: FnOnce(&mut Self) -> T>(
        &mut self,
        ident: IdentRef<'a>,
        signature: FunctionSignature<'a>,
        scope: F,
    ) -> (T, TypeCheckerFrame<'a>) {
        let signature = Arc::new(signature);

        self.top_scope_frame()
            .functions
            .insert(ident, signature.clone());

        self.define_scope(|ctx| {
            for (var_type, ident) in &signature.arguements {
                ctx.define_variable(ident, var_type.clone(), VariableKind::Local);
            }

            (scope)(ctx)
        })
    }

    pub fn define_scope<T, F: FnOnce(&mut Self) -> T>(
        &mut self,
        scope: F,
    ) -> (T, TypeCheckerFrame<'a>) {
        self.push_scope_frame();
        let ret = (scope)(self);
        let frame = self.pop_scope_frame().unwrap();

        (ret, frame)
    }

    pub fn define_variable(&mut self, ident: IdentRef<'a>, var_type: Type<'a>, kind: VariableKind) {
        self.top_scope_frame()
            .variables
            .insert(ident, (var_type, kind));
    }

    pub fn define_type(&mut self, ident: IdentRef<'a>, type_alias: Type<'a>) -> Result<()> {
        let res = self.typedefs.insert(ident, type_alias);

        match res {
            Some(_) => Err(eyre!("Type `{ident}` is defined multiple times")),
            None => Ok(()),
        }
    }

    pub fn lookup_function(&mut self, ident: IdentRef<'a>) -> Option<Arc<FunctionSignature<'a>>> {
        for frame in self.scope_stack.iter().rev() {
            if let Some(sig) = frame.functions.get(&ident) {
                return Some(sig.clone());
            }
        }

        None
    }

    pub fn lookup_variable(&mut self, var: IdentRef<'a>) -> Result<Type<'a>> {
        for (idx, frame) in self.scope_stack.iter().rev().enumerate() {
            if let Some((var_type, kind)) = frame.variables.get(var).cloned() {
                for frame in self.scope_stack.iter_mut().rev().take(idx) {
                    match kind {
                        VariableKind::Local | VariableKind::Capture => {
                            let prev = frame
                                .variables
                                .insert(var, (var_type.clone(), VariableKind::Capture));
                            assert!(prev.is_none());
                        }
                        VariableKind::Constant => {}
                    }
                }

                return Ok(var_type);
            }
        }

        Err(eyre!("Variable {var} is not in scope"))
    }

    // pub fn lookup_variable_path(&mut self, mut var_path: &[IdentRef<'a>]) -> Result<Type<'a>> {
    //     let Some(var) = var_path.split_off_first() else {
    //         return Err(eyre!("Can not look up empty variable path"));
    //     };
    //
    //     for (idx, frame) in self.scope_stack.iter().rev().enumerate() {
    //         if let Some((var_type, kind)) = frame.variables.get(var).cloned() {
    //             let mut leaf_type = var_type.clone();
    //             while let [next, rem @ ..] = var_path {
    //                 leaf_type = leaf_type.member(self, next)?;
    //                 var_path = rem
    //             }
    //
    //             // TODO: Should this capture the outer most var or inner most?
    //             for frame in self.scope_stack.iter_mut().rev().take(idx) {
    //                 match kind {
    //                     VariableKind::Local | VariableKind::Capture => {
    //                         let prev = frame
    //                             .variables
    //                             .insert(var, (var_type.clone(), VariableKind::Capture));
    //                         assert!(prev.is_none());
    //                     }
    //                     VariableKind::Constant => {}
    //                 }
    //             }
    //
    //             return Ok(leaf_type);
    //         }
    //     }
    //
    //     Err(eyre!("Variable {var}.{var_path:?} is not in scope"))
    // }
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
                *defered_type = DeferedType::ResolvedType(inner_expr.check_and_resolve_types(ctx)?);

                Ok(Type::Int)
            }
            Expr::Value(value, span) => value
                .check_and_resolve_types(ctx)
                .and_then(|it| it.resolve(ctx))
                .wrap_err("Could not type check expr value")
                .with_section(|| generate_span_error_section(*span)),
            Expr::Variable(ident, span) => {
                let var_type = ctx
                    .lookup_variable(ident)
                    .and_then(|it| it.resolve(ctx))
                    .wrap_err_with(|| format!("Could not find identifier: `{ident:?}`"))
                    .with_section(|| generate_span_error_section(*span))?;

                Ok(var_type)
            }
            Expr::Struct(map, defered_type, _span) => {
                let map = map
                    .into_iter()
                    .map(|(key, expr)| {
                        Ok((
                            *key,
                            expr.check_and_resolve_types(ctx)
                                .and_then(|it| it.resolve(ctx))?,
                        ))
                    })
                    .collect::<Result<BTreeMap<_, _>>>()?;

                *defered_type = DeferedType::ResolvedType(Type::Struct(map.clone()));

                Ok(Type::Struct(map))
            }
            Expr::Array(exprs, defered_type, span) => {
                let types = exprs
                    .into_iter()
                    .map(|expr| {
                        Ok((
                            expr.as_span(),
                            expr.check_and_resolve_types(ctx)
                                .and_then(|it| it.resolve(ctx))?,
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?;

                let mut inner_type: Option<(Span, &Type)> = None;
                for (span, expr_type) in &types {
                    if let Some((first, inner_type)) = inner_type {
                        if inner_type != expr_type {
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
                let left_type_computed = left.check_and_resolve_types(ctx)?.resolve(ctx)?;
                let right_type_computed = right.check_and_resolve_types(ctx)?.resolve(ctx)?;

                *left_type = DeferedType::ResolvedType(left_type_computed.clone());
                *right_type = DeferedType::ResolvedType(right_type_computed.clone());

                if left_type_computed.width(ctx)? != 1 || right_type_computed.width(ctx)? != 1 {
                    return Err(eyre!("Binary op only support types that are 1 word")
                        .with_section(|| generate_span_error_section(*span)));
                }

                let (valid_types, output_type) =
                    match (op, &left_type_computed, &right_type_computed) {
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
                        ) => (left == right, left.clone()),
                        (BinaryOp::Add | BinaryOp::Sub, left @ Type::Pointer(_), Type::Int) => {
                            (true, left.clone())
                        }
                        (BinaryOp::Sub, Type::Pointer(left), Type::Pointer(right)) => {
                            (left == right, Type::Int)
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
                        ) => (left == right, Type::Bool),
                        (BinaryOp::LAnd | BinaryOp::LOr, Type::Bool, Type::Bool) => {
                            (true, Type::Bool)
                        }
                        _ => (false, Type::Void),
                    };

                if !valid_types {
                    return Err(eyre!("Binary op uses a disallowed type").with_section(|| {
                        generate_span_error_section_with_annotations(
                            *span,
                            &[(
                                *span,
                                &format!(
                                    "has the type `{left_type_computed:?}`, which is not permitted"
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
                let operand_type_computed = operand.check_and_resolve_types(ctx)?.resolve(ctx)?;
                *operand_type = DeferedType::ResolvedType(operand_type_computed.clone());

                let (valid_types, return_type) = match op {
                    PrefixOp::Negate => (operand_type_computed == Type::Int, Type::Int),
                    PrefixOp::LNot => (operand_type_computed == Type::Bool, Type::Bool),
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
                let operand_type_computed = operand.check_and_resolve_types(ctx)?.resolve(ctx)?;
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
                        match &**inner_type {
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
                        let idx_type = expr.check_and_resolve_types(ctx)?.resolve(ctx)?;
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
            Expr::FunctionCall(func_call) => func_call.check_and_resolve_types(ctx)?.resolve(ctx),
            Expr::If(if_expr) => if_expr.check_and_resolve_types(ctx)?.resolve(ctx),
        }
    }
}

impl<'a> TypeCheck<'a> for FunctionCall<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
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

        for (parm_expr, (arg_type, arg_name)) in
            self.parameters.iter_mut().zip(sig.arguements.iter())
        {
            let parm_type = parm_expr.check_and_resolve_types(ctx)?.resolve(ctx)?;
            let arg_type = arg_type.resolve(ctx)?;
            if parm_type != arg_type {
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

        Ok(sig.return_type.clone())
    }
}

impl<'a> TypeCheck<'a> for FunctionDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        // Resolve types
        for (arg_type, _) in &mut self.signature.arguements {
            *arg_type = arg_type.resolve(ctx)?;
        }
        self.signature.return_type = self.signature.return_type.resolve(ctx)?;

        let (actual_return_type, frame) = ctx.define_function(
            self.function,
            FunctionSignature {
                arguements: self.signature.arguements.clone(),
                return_type: self.signature.return_type.clone(),
            },
            |ctx| self.contents.check_and_resolve_types(ctx)?.resolve(ctx),
        );

        let actual_return_type = actual_return_type?;

        if actual_return_type != self.signature.return_type.resolve(ctx)? {
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

        self.captures = DeferedCaptures::ResolvedCaptures(frame.get_captures());

        // The Function Definition it self should not have a rrtuen type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for ConstDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let actual_type = self.expr.check_and_resolve_types(ctx)?.resolve(ctx)?;

        match &mut self.var_type {
            DeferedType::ResolvedType(expected_type) => {
                *expected_type = expected_type.resolve(ctx)?;

                if &actual_type != expected_type {
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
                }
            }
            DeferedType::UnresolvedType => {
                self.var_type = DeferedType::ResolvedType(actual_type.clone());
            }
        }

        // Variable needs to be defined after we type check its expression so it cant be
        // recursively defined. (We arent trying to impl nix lol)
        ctx.define_variable(self.name, actual_type, VariableKind::Constant);

        // The const definition it self should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for LocalDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let actual_type = self.expr.check_and_resolve_types(ctx)?.resolve(ctx)?;

        match &mut self.var_type {
            DeferedType::ResolvedType(expected_type) => {
                *expected_type = expected_type.resolve(ctx)?;

                if &actual_type != expected_type {
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
                }
            }
            DeferedType::UnresolvedType => {
                self.var_type = DeferedType::ResolvedType(actual_type.clone());
            }
        }

        // Variable needs to be defined after we type check its expression so it cant be
        // recursively defined. (We arent trying to impl nix lol)
        ctx.define_variable(self.name, actual_type, VariableKind::Local);

        // The Local Definition it self should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for Assignment<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let expr_type = self.expr.check_and_resolve_types(ctx)?.resolve(ctx)?;
        let target_type = self.target.check_and_resolve_types(ctx)?.resolve(ctx)?;

        let mismatched_type = match (&target_type, &expr_type) {
            (target_type, Type::Array(array_type, _len)) if target_type != &expr_type => {
                target_type != &**array_type
            }
            (target_type, expr_type) => target_type != expr_type,
        };

        if mismatched_type {
            return Err(
                eyre!("Assignment mismatching types").with_section(|| {
                    generate_span_error_section_with_annotations(
                        self.span,
                        &[(
                            self.expr.as_span(),
                            &format!(
                                "the type `{expr_type:?}`, can not be assigned to a place of type a `{target_type:?}`",
                            ),
                        )],
                    )
                }),
            );
        }

        self.expr_type = DeferedType::ResolvedType(expr_type);
        self.target_type = DeferedType::ResolvedType(target_type);

        // The pointer assignment itself should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for Typedef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        ctx.define_type(self.name, self.type_alias.clone())?;

        // A typedef does not produce a value
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for IfCase<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let case_type = self.condition.check_and_resolve_types(ctx)?.resolve(ctx)?;
        if case_type != Type::Bool {
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

        self.contents.check_and_resolve_types(ctx)?.resolve(ctx)
    }
}

impl<'a> TypeCheck<'a> for IfExpr<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let expected_type = self
            .cases
            .first_mut()
            .unwrap()
            .check_and_resolve_types(ctx)?
            .resolve(ctx)?;

        let (rst, frame) = ctx.define_scope::<Result<_>, _>(|ctx| {
            for case in &mut self.cases {
                let case_return_type = case.check_and_resolve_types(ctx)?.resolve(ctx)?;
                if case_return_type != expected_type {
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
                let case_return_type = otherwise.check_and_resolve_types(ctx)?.resolve(ctx)?;
                if case_return_type != expected_type {
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
        });

        self.return_type = DeferedType::ResolvedType(expected_type.clone());
        self.captures = DeferedCaptures::ResolvedCaptures(frame.get_captures());

        rst.map(|_| expected_type)
    }
}

impl<'a> TypeCheck<'a> for Statement<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
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
        }
    }
}

impl<'a> TypeCheck<'a> for Block<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let mut actual_return_type = Type::Void;

        let (res, frame) = ctx.define_scope::<Result<_>, _>(|ctx| {
            for statement in &mut self.statements {
                actual_return_type = statement.check_and_resolve_types(ctx)?.resolve(ctx)?;
            }

            Ok(())
        });

        self.captures = DeferedCaptures::ResolvedCaptures(frame.get_captures());

        res.map(|()| actual_return_type)
    }
}
