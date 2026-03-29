use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Debug, Display},
    sync::Arc,
};

use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Result, eyre},
};
use tracing::instrument;

use crate::{
    ast::{
        AsSpan, BinaryOp, Block, Captures, ConstDef, DeferedCaptures, DeferedType, Expr,
        FunctionCall, FunctionDef, FunctionSignature, IdentRef, IfCase, IfExpr, LocalDef,
        PtrAssign, Punctuation, Statement, Type, Typedef, UnaryOp, Value,
    },
    codegen::builtins::clac_builtins,
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

    pub fn lookup_variable_path(&mut self, mut var_path: &[IdentRef<'a>]) -> Result<Type<'a>> {
        let Some(var) = var_path.split_off_first() else {
            return Err(eyre!("Can not look up empty variable path"));
        };

        for (idx, frame) in self.scope_stack.iter().rev().enumerate() {
            if let Some((var_type, kind)) = frame.variables.get(var).cloned() {
                let mut leaf_type = var_type.clone();
                while let [next, ..] = var_path {
                    leaf_type = leaf_type.member(self, next)?;
                }

                // TODO: Should this capture the outer most var or inner most?
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

                return Ok(leaf_type);
            }
        }

        Err(eyre!("Variable {var}.{var_path:?} is not in scope"))
    }
}

pub trait TypeCheck<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>>;
}

impl<'a> TypeCheck<'a> for Value<'a> {
    #[instrument(name = "typecheck_value", fields(%self, %ctx))]
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker) -> Result<Type<'a>> {
        Ok(self.compute_type())
    }
}

impl<'a> TypeCheck<'a> for Expr<'a> {
    #[instrument(name = "typecheck_expr", fields(%self, %ctx))]
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        match self {
            Expr::Value(value, span) => value
                .check_and_resolve_types(ctx)
                .wrap_err("Could not type check expr value")
                .with_section(|| generate_span_error_section(*span)),
            Expr::Path(ident, span) => {
                let var_type = ctx
                    .lookup_variable_path(ident)
                    .wrap_err_with(|| format!("Could not find identifier: `{ident:?}`"))
                    .with_section(|| generate_span_error_section(*span))?;

                Ok(var_type)
            }
            Expr::BinaryOp {
                op,
                left,
                right,
                span,
                left_type,
                right_type,
            } => {
                let left_type_computed = left.check_and_resolve_types(ctx)?;
                let right_type_computed = right.check_and_resolve_types(ctx)?;

                *left_type = DeferedType::ResolvedType(left_type_computed.clone());
                *right_type = DeferedType::ResolvedType(right_type_computed.clone());

                if left_type_computed != right_type_computed {
                    return Err(eyre!("Binary op has differing left and right types")
                        .with_section(|| {
                            generate_span_error_section_with_annotations(
                                *span,
                                &[
                                    (
                                        left.as_span(),
                                        &format!("has the type `{left_type_computed:?}`"),
                                    ),
                                    (
                                        right.as_span(),
                                        &format!("has differing type `{right_type_computed:?}`"),
                                    ),
                                ],
                            )
                        }));
                }

                let allowed_type = match op {
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod
                    | BinaryOp::Pow
                    | BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Le
                    | BinaryOp::Ge
                    | BinaryOp::Lt
                    | BinaryOp::Gt
                    | BinaryOp::BShr
                    | BinaryOp::BShl
                    | BinaryOp::BAnd => Type::Int,

                    BinaryOp::LAnd | BinaryOp::LOr => Type::Bool,
                };

                if left_type_computed != allowed_type {
                    return Err(eyre!("Binary op uses a disallowed type")
                        .with_section(|| {
                            generate_span_error_section_with_annotations(
                                *span,
                                &[
                                    (*span, &format!("has the type `{left_type_computed:?}`, but only the type `{allowed_type:?}` is permitted")),
                                ],
                            )
                        }));
                }

                let output_type = match op {
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod
                    | BinaryOp::Pow
                    | BinaryOp::BShr
                    | BinaryOp::BShl
                    | BinaryOp::BAnd => Type::Int,

                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Le
                    | BinaryOp::Ge
                    | BinaryOp::Lt
                    | BinaryOp::Gt
                    | BinaryOp::LAnd
                    | BinaryOp::LOr => Type::Bool,
                };

                Ok(output_type)
            }
            Expr::UnaryOp {
                op,
                operand,
                span,
                operand_type,
            } => {
                let operand_type_computed = operand.check_and_resolve_types(ctx)?;
                *operand_type = DeferedType::ResolvedType(operand_type_computed.clone());

                let (allowed_type, return_type) = match op {
                    UnaryOp::Negate => (Type::Int, Type::Int),
                    UnaryOp::LNot => (Type::Bool, Type::Bool),
                    UnaryOp::Cast(to) => {
                        if operand_type_computed.width(ctx)? == to.width(ctx)? {
                            (operand_type_computed.clone(), to.clone())
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
                    UnaryOp::Dereference => {
                        if let Type::Pointer(target) = operand_type_computed.clone() {
                            (operand_type_computed.clone(), *target)
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

                if operand_type_computed != allowed_type {
                    return Err(eyre!("Unary op uses a disallowed type")
                        .with_section(|| {
                            generate_span_error_section_with_annotations(
                                *span,
                                &[
                                    (*span, &format!("has the type `{operand_type_computed:?}`, but only the type `{allowed_type:?}` is permitted")),
                                ],
                            )
                        }));
                }

                Ok(return_type)
            }
            Expr::FunctionCall(func_call) => func_call.check_and_resolve_types(ctx),
            Expr::If(if_expr) => if_expr.check_and_resolve_types(ctx),
        }
    }
}

impl<'a> TypeCheck<'a> for FunctionCall<'a> {
    #[instrument(name = "typecheck_func_call", fields(%self, %ctx))]
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
            let parm_type = parm_expr.check_and_resolve_types(ctx)?;
            if parm_type != *arg_type {
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
    #[instrument(name = "typecheck_func_def", fields(%self, %ctx))]
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let (actual_return_type, frame) = ctx.define_function(
            self.function,
            FunctionSignature {
                arguements: self.signature.arguements.clone(),
                return_type: self.signature.return_type.clone(),
            },
            |ctx| self.contents.check_and_resolve_types(ctx),
        );

        let actual_return_type = actual_return_type?;

        if actual_return_type != self.signature.return_type {
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
    #[instrument(name = "typecheck_const_def", fields(%self, %ctx))]
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let actual_type = self.expr.check_and_resolve_types(ctx)?;
        if actual_type != self.var_type {
            return Err(
                eyre!("Const definition set to the incorrect type").with_section(|| {
                    generate_span_error_section_with_annotations(
                        self.span,
                        &[(
                            self.expr_span,
                            &format!(
                                "has the type `{actual_type:?}`, but a `{:?}` is required",
                                self.var_type
                            ),
                        )],
                    )
                }),
            );
        }

        // Variable needs to be defined after we type check its expression so it cant be
        // recursively defined. (We arent trying to impl nix lol)
        ctx.define_variable(self.name, self.var_type.clone(), VariableKind::Constant);

        // The const definition it self should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for LocalDef<'a> {
    #[instrument(name = "typecheck_local_def", fields(%self, %ctx))]
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let actual_type = self.expr.check_and_resolve_types(ctx)?;
        if actual_type != self.var_type {
            return Err(
                eyre!("Local definition set to the incorrect type").with_section(|| {
                    generate_span_error_section_with_annotations(
                        self.span,
                        &[(
                            self.expr.as_span(),
                            &format!(
                                "has the type `{actual_type:?}`, but a `{:?}` is required",
                                self.var_type
                            ),
                        )],
                    )
                }),
            );
        }

        // Variable needs to be defined after we type check its expression so it cant be
        // recursively defined. (We arent trying to impl nix lol)
        ctx.define_variable(self.name, self.var_type.clone(), VariableKind::Local);

        // The Local Definition it self should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for PtrAssign<'a> {
    #[instrument(name = "typecheck_ptr_assign", fields(%self, %ctx))]
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let expr_type = self.expr.check_and_resolve_types(ctx)?;
        let target_type = self.target.check_and_resolve_types(ctx)?;

        let Type::Pointer(target_type) = target_type else {
            return Err(
                eyre!("Assignment only support pointer types").with_section(|| {
                    generate_span_error_section_with_annotations(
                        self.span,
                        &[(
                            self.expr.as_span(),
                            &format!("the type `{target_type:?}`, is not a pointer type",),
                        )],
                    )
                }),
            );
        };

        if *target_type != expr_type {
            return Err(
                eyre!("Pointer assignment mismatching types").with_section(|| {
                    generate_span_error_section_with_annotations(
                        self.span,
                        &[(
                            self.expr.as_span(),
                            &format!(
                                "the type `{expr_type:?}`, can not be assigned to a pointer of type a `{target_type:?}`",
                            ),
                        )],
                    )
                }),
            );
        }

        self.value_type = DeferedType::ResolvedType(expr_type);

        // The pointer assignment it self should not have a return type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for Typedef<'a> {
    #[instrument(name = "typecheck_type_def", fields(%self, %ctx))]
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        ctx.define_type(self.name, self.type_alias.clone())?;

        // A typedef does not produce a value
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for IfCase<'a> {
    #[instrument(name = "typecheck_if_case", fields(%self, %ctx))]
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let case_type = self.condition.check_and_resolve_types(ctx)?;
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

        self.contents.check_and_resolve_types(ctx)
    }
}

impl<'a> TypeCheck<'a> for IfExpr<'a> {
    #[instrument(name = "typecheck_if_expr", fields(%self, %ctx))]
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let expected_type = self
            .cases
            .first_mut()
            .unwrap()
            .check_and_resolve_types(ctx)?;

        let (rst, frame) = ctx.define_scope::<Result<_>, _>(|ctx| {
            for case in &mut self.cases {
                let case_return_type = case.check_and_resolve_types(ctx)?;
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
                                    Type::Bool
                                ),
                            )],
                        )
                    }),
                );
                }
            }

            if let Some(otherwise) = &mut self.otherwise {
                let case_return_type = otherwise.check_and_resolve_types(ctx)?;
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
                                    Type::Bool
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
    #[instrument(name = "typecheck_statement", fields(%self, %ctx))]
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
            Statement::PtrAssign(ptr_assign) => ptr_assign.check_and_resolve_types(ctx),
            Statement::Typedef(typedef) => typedef.check_and_resolve_types(ctx),
        }
    }
}

impl<'a> TypeCheck<'a> for Block<'a> {
    #[instrument(name = "typecheck_block", fields(%self, %ctx))]
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type<'a>> {
        let mut actual_return_type = Type::Void;

        let (res, frame) = ctx.define_scope::<Result<_>, _>(|ctx| {
            for statement in &mut self.statements {
                actual_return_type = statement.check_and_resolve_types(ctx)?;
            }

            Ok(())
        });

        self.captures = DeferedCaptures::ResolvedCaptures(frame.get_captures());

        res.map(|()| actual_return_type)
    }
}
