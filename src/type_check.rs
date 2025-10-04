// TODO: Make type check use a different context than code gen context, and try to get rid of guess_type
// The context should be able to store the signatures of variables and functions ad it traversed
// the ast during type checking

use std::{collections::HashMap, sync::Arc};

use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Result, eyre},
};

use crate::{
    ast::{
        AsSpan, BinaryOp, Block, DeferedType, Expr, FunctionCall, FunctionDef, IdentRef, IfCase,
        IfExpr, LocalDef, Punctuation, Statement, StaticDef, Type, UnaryOp, Value,
    },
    codegen::{CodegenCtx, FunctionSignature},
    middleware::{generate_span_error_section, generate_span_error_section_with_annotations},
};

#[derive(Debug, Clone)]
pub struct TypeCheckerFrame<'a> {
    pub variables: HashMap<IdentRef<'a>, Type>,
    pub functions: HashMap<IdentRef<'a>, Arc<FunctionSignature<'a>>>,
}

#[derive(Debug, Clone)]
pub struct TypeChecker<'a> {
    pub scope_stack: Vec<TypeCheckerFrame<'a>>,
}

impl Default for TypeChecker<'_> {
    fn default() -> Self {
        let codegen = CodegenCtx::default();

        let mut type_checker = Self {
            scope_stack: vec![TypeCheckerFrame {
                variables: Default::default(),
                functions: codegen
                    .builtins
                    .into_iter()
                    .map(|(key, (_, value))| {
                        (
                            // TODO: can we get this to work without leaking the string?
                            &*key.leak(),
                            value.clone(),
                        )
                    })
                    .collect(),
            }],
        };

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

        let old_frame = self.scope_stack.pop();

        old_frame
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
    ) -> T {
        let signature = Arc::new(signature);

        self.top_scope_frame()
            .functions
            .insert(ident, signature.clone());

        {
            self.push_scope_frame();
            for (var_type, ident) in &signature.arguements {
                self.define_variable(ident, *var_type);
            }

            let ret = (scope)(self);

            self.pop_scope_frame().unwrap();

            ret
        }
    }

    pub fn define_variable(&mut self, ident: IdentRef<'a>, var_type: Type) {
        self.top_scope_frame().variables.insert(ident, var_type);
    }

    pub fn lookup_function(&self, ident: IdentRef<'a>) -> Option<&FunctionSignature<'a>> {
        for frame in self.scope_stack.iter().rev() {
            if let Some(sig) = frame.functions.get(&ident) {
                return Some(sig);
            }
        }

        None
    }

    pub fn lookup_variable(&self, ident: IdentRef<'a>) -> Option<Type> {
        for frame in self.scope_stack.iter().rev() {
            if let Some(var_type) = frame.variables.get(ident) {
                return Some(*var_type);
            }
        }

        None
    }
}

pub trait TypeCheck<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type>;
}

impl TypeCheck<'_> for Value {
    fn check_and_resolve_types(&mut self, _ctx: &mut TypeChecker) -> Result<Type> {
        match self {
            Value::Int(_) => Ok(Type::Int),
            Value::Bool(_) => Ok(Type::Bool),
        }
    }
}

impl<'a> TypeCheck<'a> for Expr<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type> {
        match self {
            Expr::Value(value, span) => value
                .check_and_resolve_types(ctx)
                .wrap_err_with(|| format!("Could not type check expr value"))
                .with_section(|| generate_span_error_section(*span)),
            Expr::Ident(ident, span) => {
                let var_type = ctx
                    .lookup_variable(ident)
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

                let output_type = match op {
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod
                    | BinaryOp::Pow => Type::Int,

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
}

impl<'a> TypeCheck<'a> for FunctionCall<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type> {
        let sig = ctx
            .lookup_function(self.function)
            .wrap_err_with(|| format!("Could not find function: {}", self.function))
            .with_section(|| generate_span_error_section(self.span))?
            // TODO: Avoid clone
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

        Ok(sig.return_type)
    }
}

impl<'a> TypeCheck<'a> for FunctionDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type> {
        let actual_return_type = ctx.define_function(
            self.function,
            FunctionSignature {
                arguements: self.arguements.clone(),
                return_type: self.return_type,
            },
            |ctx| self.contents.check_and_resolve_types(ctx),
        )?;

        if actual_return_type != self.return_type {
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
                                self.return_type
                            ),
                        )],
                    )
                })
                .with_section(|| {
                    format!("Last statement: {:#?}", self.contents.statements.last())
                }));
        }

        // The Function Definition it self should not have a rrtuen type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for StaticDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type> {
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

        // Variable needs to be defined after we type check its expression so it cant be
        // recursively defined. (We arent trying to impl nix lol)
        ctx.define_variable(self.name, self.var_type);

        // The Static Definition it self should not have a rrtuen type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for LocalDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type> {
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
        ctx.define_variable(self.name, self.var_type);

        // The Local Definition it self should not have a rrtuen type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for IfCase<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type> {
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
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type> {
        let expected_type = self
            .cases
            .first_mut()
            .unwrap()
            .check_and_resolve_types(ctx)?;

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

        self.return_type = DeferedType::ResolvedType(expected_type);

        Ok(expected_type)
    }
}

impl<'a> TypeCheck<'a> for Statement<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type> {
        match self {
            Statement::FunctionDef(function_def) => function_def.check_and_resolve_types(ctx),
            Statement::Static(static_def) => static_def.check_and_resolve_types(ctx),
            Statement::Local(local_def) => local_def.check_and_resolve_types(ctx),
            Statement::Expr(expr, Punctuation::Unpunctuated) => expr.check_and_resolve_types(ctx),
            Statement::Expr(expr, Punctuation::Punctuated) => {
                expr.check_and_resolve_types(ctx)?;
                Ok(Type::Void)
            }
        }
    }
}

impl<'a> TypeCheck<'a> for Block<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type> {
        let mut actual_return_type = Type::Void;

        for statement in &mut self.statements {
            actual_return_type = statement.check_and_resolve_types(ctx)?;
        }

        Ok(actual_return_type)
    }
}
