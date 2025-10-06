use std::{collections::HashMap, sync::Arc};

use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Result, eyre},
};

use crate::{
    ast::{
        AsSpan, BinaryOp, Block, Captures, ConstDef, DeferedCaptures, DeferedType, Expr,
        FunctionCall, FunctionDef, IdentRef, IfCase, IfExpr, LocalDef, Punctuation, Statement,
        Type, UnaryOp, Value,
    },
    codegen::{builtins::clac_builtins, ir::FunctionSignature},
    middleware::{generate_span_error_section, generate_span_error_section_with_annotations},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariableKind {
    Local,
    Constant,
    Capture,
}

#[derive(Debug, Clone)]
pub struct TypeCheckerFrame<'a> {
    pub variables: HashMap<IdentRef<'a>, (Type, VariableKind)>,
    pub functions: HashMap<IdentRef<'a>, Arc<FunctionSignature<'a>>>,
}

impl<'a> TypeCheckerFrame<'a> {
    pub fn get_captures(&self) -> Captures<'a> {
        Captures {
            captures: self
                .variables
                .iter()
                .filter(|(_, (_, kind))| *kind == VariableKind::Capture)
                .map(|(ident, (data_type, _))| (*ident, *data_type))
                .collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeChecker<'a> {
    pub scope_stack: Vec<TypeCheckerFrame<'a>>,
}

impl Default for TypeChecker<'_> {
    fn default() -> Self {
        let mut type_checker = Self {
            scope_stack: vec![],
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
                ctx.define_variable(ident, *var_type, VariableKind::Local);
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

    pub fn define_variable(&mut self, ident: IdentRef<'a>, var_type: Type, kind: VariableKind) {
        self.top_scope_frame()
            .variables
            .insert(ident, (var_type, kind));
    }

    pub fn lookup_function(&mut self, ident: IdentRef<'a>) -> Option<Arc<FunctionSignature<'a>>> {
        for frame in self.scope_stack.iter().rev() {
            if let Some(sig) = frame.functions.get(&ident) {
                return Some(sig.clone());
            }
        }

        None
    }

    pub fn lookup_variable(&mut self, ident: IdentRef<'a>) -> Option<Type> {
        for (idx, frame) in self.scope_stack.iter().rev().enumerate() {
            if let Some((var_type, kind)) = frame.variables.get(ident).copied() {
                for frame in self.scope_stack.iter_mut().rev().take(idx) {
                    match kind {
                        VariableKind::Local | VariableKind::Capture => {
                            let prev = frame
                                .variables
                                .insert(ident, (var_type, VariableKind::Capture));
                            assert!(prev.is_none());
                        }
                        VariableKind::Constant => {}
                    }
                }

                return Some(var_type);
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
                .wrap_err("Could not type check expr value")
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
                    | BinaryOp::Gt
                    | BinaryOp::BShr
                    | BinaryOp::BShl
                    | BinaryOp::BAnd => Type::Int,

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
        let (actual_return_type, frame) = ctx.define_function(
            self.function,
            FunctionSignature {
                arguements: self.arguements.clone(),
                return_type: self.return_type,
            },
            |ctx| self.contents.check_and_resolve_types(ctx),
        );

        let actual_return_type = actual_return_type?;

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

        self.captures = DeferedCaptures::ResolvedCaptures(frame.get_captures());

        // The Function Definition it self should not have a rrtuen type
        Ok(Type::Void)
    }
}

impl<'a> TypeCheck<'a> for ConstDef<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type> {
        let actual_type = self.value.check_and_resolve_types(ctx)?;
        if actual_type != self.var_type {
            return Err(
                eyre!("Const definition set to the incorrect type").with_section(|| {
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
        ctx.define_variable(self.name, self.var_type, VariableKind::Constant);

        // The const definition it self should not have a retuen type
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
        ctx.define_variable(self.name, self.var_type, VariableKind::Local);

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

        self.return_type = DeferedType::ResolvedType(expected_type);
        self.captures = DeferedCaptures::ResolvedCaptures(frame.get_captures());

        rst.map(|()| expected_type)
    }
}

impl<'a> TypeCheck<'a> for Statement<'a> {
    fn check_and_resolve_types(&mut self, ctx: &mut TypeChecker<'a>) -> Result<Type> {
        match self {
            Statement::FunctionDef(function_def) => function_def.check_and_resolve_types(ctx),
            Statement::Const(const_def) => const_def.check_and_resolve_types(ctx),
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
