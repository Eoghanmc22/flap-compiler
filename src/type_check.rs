use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Result, bail, eyre},
};

use crate::{
    ast::{
        AsSpan, BinaryOp, Block, Expr, FunctionCall, FunctionDef, IfCase, IfExpr, LocalDef,
        Statement, StaticDef, Type, UnaryOp, Value,
    },
    codegen::CodegenCtx,
    middleware::{generate_span_error_section, generate_span_error_section_with_annotations},
};

pub trait TypeCheck {
    fn check_and_resolve_types(&self, ctx: &CodegenCtx) -> Result<Type>;

    fn guess_type(&self) -> Option<Type>;
}

impl TypeCheck for Value {
    fn check_and_resolve_types(&self, _ctx: &CodegenCtx) -> Result<Type> {
        match self {
            Value::Int(_) => Ok(Type::Int),
            Value::Bool(_) => Ok(Type::Bool),
        }
    }

    fn guess_type(&self) -> Option<Type> {
        match self {
            Value::Int(_) => Some(Type::Int),
            Value::Bool(_) => Some(Type::Bool),
        }
    }
}

impl TypeCheck for Expr<'_> {
    fn check_and_resolve_types(&self, ctx: &CodegenCtx) -> Result<Type> {
        match self {
            Expr::Value(value, span) => value
                .check_and_resolve_types(ctx)
                .wrap_err_with(|| format!("Could not type check expr value"))
                .with_section(|| generate_span_error_section(*span)),
            Expr::Ident(ident, span) => {
                let (_data_ref, var_type) = ctx
                    .lookup_ident_data_ref(ident)
                    .wrap_err_with(|| format!("Could not find identifier: `{ident}`"))
                    .with_section(|| generate_span_error_section(*span))?;

                Ok(var_type)
            }
            Expr::BinaryOp {
                op,
                left,
                right,
                span,
            } => {
                let left_type = left.check_and_resolve_types(ctx)?;
                let right_type = right.check_and_resolve_types(ctx)?;

                if left_type != right_type {
                    return Err(eyre!("Binary op has differing left and right types")
                        .with_section(|| {
                            generate_span_error_section_with_annotations(
                                *span,
                                &[
                                    (left.as_span(), &format!("has the type `{left_type:?}`")),
                                    (
                                        right.as_span(),
                                        &format!("has differing type `{right_type:?}`"),
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
                    | BinaryOp::Gt => Type::Int,

                    BinaryOp::LAnd | BinaryOp::LOr => Type::Bool,
                };

                if left_type != allowed_type {
                    return Err(eyre!("Binary op uses a disallowed type")
                        .with_section(|| {
                            generate_span_error_section_with_annotations(
                                *span,
                                &[
                                    (*span, &format!("has the type `{left_type:?}`, but only the type `{allowed_type:?}` is permitted")),
                                ],
                            )
                        }));
                }

                Ok(left_type)
            }
            Expr::UnaryOp { op, operand, span } => {
                let operand_type = operand.check_and_resolve_types(ctx)?;

                let allowed_type = match op {
                    UnaryOp::Negate => Type::Int,
                    UnaryOp::LNot => Type::Bool,
                };

                if operand_type != allowed_type {
                    return Err(eyre!("Unary op uses a disallowed type")
                        .with_section(|| {
                            generate_span_error_section_with_annotations(
                                *span,
                                &[
                                    (*span, &format!("has the type `{operand_type:?}`, but only the type `{allowed_type:?}` is permitted")),
                                ],
                            )
                        }));
                }

                Ok(operand_type)
            }
            Expr::FunctionCall(func_call) => func_call.check_and_resolve_types(ctx),
            Expr::If(if_expr) => if_expr.check_and_resolve_types(ctx),
        }
    }

    fn guess_type(&self) -> Option<Type> {
        match self {
            Expr::Value(value, _) => value.guess_type(),
            Expr::Ident(_, _) => None,
            Expr::BinaryOp { left, right, .. } => {
                let left_type = left.guess_type();
                let right_type = right.guess_type();

                match (left_type, right_type) {
                    // TODO: Is there a better stratagy thsn just choosing one?
                    (Some(left_type), Some(_right_type)) => Some(left_type),
                    (Some(var_type), None) | (None, Some(var_type)) => Some(var_type),
                    (None, None) => None,
                }
            }
            Expr::UnaryOp { operand, .. } => operand.guess_type(),
            Expr::FunctionCall(function_call) => function_call.guess_type(),
            Expr::If(if_expr) => if_expr.guess_type(),
        }
    }
}

impl TypeCheck for FunctionCall<'_> {
    fn check_and_resolve_types(&self, ctx: &CodegenCtx) -> Result<Type> {
        let sig = ctx
            .lookup_function_like_signature(self.function)
            .wrap_err_with(|| format!("Could not find function: {}", self.function))
            .with_section(|| generate_span_error_section(self.span))?;

        for (parm_expr, (arg_type, arg_name)) in self.paramaters.iter().zip(sig.arguements.iter()) {
            let parm_type = parm_expr.check_and_resolve_types(ctx)?;
            if parm_type != *arg_type {
                return Err(eyre!("Function called with a paramater of the incorrect type")
                            .with_section(|| {
                                generate_span_error_section_with_annotations(
                                    self.span,
                                    &[
                                        (parm_expr.as_span(), &format!("has the type `{parm_expr:?}`, but the arguemment `{arg_name}` to the function `{}` expected the type `{arg_type:?}`", self.function)),
                                    ],
                                )
                            }));
            }
        }

        Ok(sig.return_type)
    }

    fn guess_type(&self) -> Option<Type> {
        // We just dont know...
        None
    }
}

impl TypeCheck for FunctionDef<'_> {
    fn check_and_resolve_types(&self, ctx: &CodegenCtx) -> Result<Type> {
        let actual_return_type = self.contents.check_and_resolve_types(ctx)?;
        if actual_return_type != self.return_type {
            return Err(
                eyre!("Function definition returns the incorrect type").with_section(|| {
                    generate_span_error_section_with_annotations(
                        self.span,
                        &[(
                            self.contents
                                .statements
                                .last()
                                .map(|it| it.as_span())
                                .unwrap_or_else(|| self.contents.as_span()),
                            &format!(
                                "has the type `{actual_return_type:?}`, but a `{:?}` is required",
                                self.return_type
                            ),
                        )],
                    )
                }),
            );
        }

        // The Function Definition it self should not have a rrtuen type
        Ok(Type::Void)
    }

    fn guess_type(&self) -> Option<Type> {
        Some(Type::Void)
    }
}

impl TypeCheck for StaticDef<'_> {
    fn check_and_resolve_types(&self, ctx: &CodegenCtx) -> Result<Type> {
        let actual_type = self.value.check_and_resolve_types(ctx)?;
        if actual_type != self.var_type {
            return Err(
                eyre!("Static definition set to the incorrect type").with_section(|| {
                    generate_span_error_section_with_annotations(
                        self.span,
                        &[(
                            self.value_span,
                            &format!(
                                "has the type `{actual_type:?}`, but a `{:?}` is required",
                                self.var_type
                            ),
                        )],
                    )
                }),
            );
        }

        // The Static Definition it self should not have a rrtuen type
        Ok(Type::Void)
    }

    fn guess_type(&self) -> Option<Type> {
        Some(Type::Void)
    }
}

impl TypeCheck for LocalDef<'_> {
    fn check_and_resolve_types(&self, ctx: &CodegenCtx) -> Result<Type> {
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

        // The Local Definition it self should not have a rrtuen type
        Ok(Type::Void)
    }

    fn guess_type(&self) -> Option<Type> {
        Some(Type::Void)
    }
}

impl TypeCheck for IfCase<'_> {
    fn check_and_resolve_types(&self, ctx: &CodegenCtx) -> Result<Type> {
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

    fn guess_type(&self) -> Option<Type> {
        Some(self.contents.return_type)
    }
}

impl TypeCheck for IfExpr<'_> {
    fn check_and_resolve_types(&self, ctx: &CodegenCtx) -> Result<Type> {
        for case in &self.cases {
            let case_return_type = case.check_and_resolve_types(ctx)?;
            if case_return_type != self.return_type {
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

            if case_return_type != case.contents.return_type {
                // TODO: Better error message? Does this error even matter?
                bail!("Type checking failed")
            }
        }

        if let Some(otherwise) = &self.otherwise {
            let case_return_type = otherwise.check_and_resolve_types(ctx)?;
            if case_return_type != self.return_type {
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

        Ok(self.return_type)
    }

    fn guess_type(&self) -> Option<Type> {
        Some(self.return_type)
    }
}

impl TypeCheck for Statement<'_> {
    fn check_and_resolve_types(&self, ctx: &CodegenCtx) -> Result<Type> {
        match self {
            Statement::Expr(expr) => expr.check_and_resolve_types(ctx),
            Statement::FunctionDef(function_def) => function_def.check_and_resolve_types(ctx),
            Statement::Static(static_def) => static_def.check_and_resolve_types(ctx),
            Statement::Local(local_def) => local_def.check_and_resolve_types(ctx),
        }
    }

    fn guess_type(&self) -> Option<Type> {
        match self {
            Statement::Expr(expr) => expr.guess_type(),
            Statement::FunctionDef(function_def) => function_def.guess_type(),
            Statement::Static(static_def) => static_def.guess_type(),
            Statement::Local(local_def) => local_def.guess_type(),
        }
    }
}

impl TypeCheck for Block<'_> {
    fn check_and_resolve_types(&self, ctx: &CodegenCtx) -> Result<Type> {
        let mut actual_return_type = Type::Void;

        for statement in &self.statements {
            actual_return_type = statement.check_and_resolve_types(ctx)?;
        }

        if actual_return_type != self.return_type {
            // TODO: Better error message? Does this error even matter?
            bail!("Type checking failed")
        }

        Ok(actual_return_type)
    }

    fn guess_type(&self) -> Option<Type> {
        Some(self.return_type)
    }
}
