use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Ok, Result, eyre},
};
use pest::Span;
use std::{collections::BTreeMap, fmt::Write};
use tracing::trace;

use crate::{
    ast::{
        AsSpan, Assignment, BinaryOp, Block, ConstDef, DeferedType, DeferedVersion, Expr,
        FunctionCall, FunctionDef, FunctionSignature, IfCase, IfExpr, LocalDef, Loop, PostfixOp,
        PrefixOp, Punctuation, SizeOfMode, Statement, Stride, Type, Value,
    },
    codegen::{
        AnnotatedDataRef, CodegenCtx, MaybeTailCall, Offset,
        clac::{ClacProgram, ClacToken, ClacValue},
        ir::{ClacOp, DataReference},
    },
};

pub fn walk_block<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    block: &Block<'a>,
) -> Result<MaybeTailCall<'a>> {
    let mut last_return_val: Option<ExpressionOutput> = None;

    let mut defered = Vec::new();

    for statement in &block.statements {
        if let Some(last_return_val) = last_return_val {
            last_return_val.into_data_ref(ctx)?;
        }

        last_return_val = match statement {
            Statement::Const(const_def) => {
                walk_const_def(ctx, const_def)?;
                None
            }
            Statement::Local(local_def) => {
                walk_local_def(ctx, local_def)?;
                None
            }
            Statement::FunctionDef(function_def) => {
                walk_function_def(ctx, function_def)?;
                None
            }
            Statement::Expr(expr, Punctuation::Unpunctuated) => Some(walk_expr(ctx, expr)?),
            Statement::Expr(expr, Punctuation::Punctuated) => {
                walk_expr(ctx, expr)?.into_data_ref(ctx)?;
                None
            }
            Statement::Assignment(assignment) => {
                walk_assignment(ctx, assignment)?.into_data_ref(ctx)?;
                None
            }
            Statement::Typedef(_) => None,
            Statement::Defer(block) => {
                defered.push(block);
                None
            }
            Statement::Loop(inner) => Some(ExpressionOutput::TailCall(walk_loop(ctx, inner)?)),
        }
    }

    let ret = if let Some(last_return_val) = last_return_val {
        last_return_val.into_tail_call(ctx)?
    } else {
        DataReference::Tempoary(ctx.allocate_tempoary(Type::Void)?, None).into()
    };

    // TODO: need to handle this in early return paths if we ever add that
    if !defered.is_empty() {
        let ret = ret.into_data_ref(ctx)?;

        for defered in defered.into_iter().rev() {
            walk_block(ctx, defered)?.into_data_ref(ctx)?;
        }

        Ok(ret.into())
    } else {
        Ok(ret)
    }
}

fn walk_function_call<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    func_call: &FunctionCall<'a>,
) -> Result<MaybeTailCall<'a>> {
    let FunctionCall {
        function,
        parameters,
        span,
    } = func_call;

    let parameters = parameters
        .iter()
        .map(|it| walk_expr(ctx, it)?.into_data_ref(ctx))
        .collect::<Result<Vec<DataReference<'a>>>>()?;

    ctx.call_function_like(function, parameters, *span)
        .wrap_err_with(|| format!("Walk function call '{:?}' failed", function))
        .with_section(|| generate_span_error_section(*span))
}

fn walk_function_def<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    func_def: &FunctionDef<'a>,
) -> Result<()> {
    let FunctionDef {
        attributes,
        function,
        contents,
        span,
        signature,
    } = func_def;

    ctx.define_function(function, signature.clone(), attributes, move |ctx| {
        walk_block(ctx, contents)
    })
    .wrap_err_with(|| format!("Walk function def '{:?}' failed", function))
    .with_section(|| generate_span_error_section(*span))?;

    Ok(())
}

fn walk_const_def<'a, 'b>(ctx: &mut CodegenCtx<'a, 'b>, const_def: &ConstDef<'a>) -> Result<()> {
    let ConstDef {
        var_type,
        expr,
        version,
        ..
    } = const_def;

    let expr_data_ref = walk_expr(ctx, expr)?.into_data_ref(ctx)?;
    let expr_data_ref = ctx.dereference_data_ref(&expr_data_ref)?;
    let expr_value = match expr_data_ref {
        DataReference::Value(val, _) => val,
        _ => {
            return Err(eyre!("Const could not be evaluated at compile time"))
                .with_section(|| generate_span_error_section(const_def.as_span()));
        }
    };

    let DeferedType::ResolvedType(var_type) = var_type else {
        return Err(eyre!("COMPILER BUG: defered type was not resolved"));
    };

    let DeferedVersion::ResolvedVersion(version) = version else {
        return Err(eyre!("COMPILER BUG: defered version was not resolved"));
    };

    assert!(var_type.compatible_with(&expr_value.compute_type(), ctx.type_checker)?);

    ctx.define_const(*version, expr_value);

    Ok(())
}

fn walk_local_def<'a, 'b>(ctx: &mut CodegenCtx<'a, 'b>, local_def: &LocalDef<'a>) -> Result<()> {
    let LocalDef {
        var_type,
        expr,
        version,
        ..
    } = local_def;

    let DeferedType::ResolvedType(var_type) = var_type.clone() else {
        return Err(eyre!("COMPILER BUG: defered type was not resolved"));
    };

    let DeferedVersion::ResolvedVersion(version) = version else {
        return Err(eyre!("COMPILER BUG: defered version was not resolved"));
    };

    let data_ref = walk_expr(ctx, &expr)?.into_data_ref(ctx)?;
    ctx.promote_to_local(&data_ref, *version, var_type)?;

    Ok(())
}

fn walk_assignment<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    assignment: &Assignment<'a>,
) -> Result<MaybeTailCall<'a>> {
    let Assignment {
        target,
        expr,
        span,
        expr_span: _,
        target_type,
        expr_type,
    } = assignment;
    let DeferedType::ResolvedType(target_type) = target_type.clone() else {
        return Err(eyre!("COMPILER BUG: defered type was not resolved"));
    };
    let DeferedType::ResolvedType(expr_type) = expr_type.clone() else {
        return Err(eyre!("COMPILER BUG: defered type was not resolved"));
    };

    let expr_data_ref = walk_expr(ctx, &expr)?.into_data_ref(ctx)?;
    let target_place = walk_expr(ctx, &target)?;

    match target_place {
        ExpressionOutput::TailCall(maybe_tail_call) => {
            assert!(target_type.compatible_with(&expr_type, ctx.type_checker)?);

            if let Some(derived_from_local) = maybe_tail_call.into_data_ref(ctx)?.originator() {
                let Some(old) = ctx.lookup_local(&derived_from_local.version) else {
                    if let Some(_) = ctx.lookup_const(&derived_from_local.version) {
                        return Err(eyre!(
                            "Can not assign to a place derived from a constant since constants are immutable",
                        )
                        .with_section(|| generate_span_error_section(*span)));
                    } else {
                        return Err(eyre!(
                            "COMPILER BUG: Attempted to assign to non existant variable",
                        )
                        .with_section(|| generate_span_error_section(*span)));
                    }
                };

                if derived_from_local.offset == Offset(0)
                    && old
                        .data_type
                        .compatible_with(&expr_type, ctx.type_checker)?
                {
                    ctx.promote_to_local(&expr_data_ref, derived_from_local.version, target_type)?;
                } else {
                    return Err(eyre!(
                        "UNIMPLEMENTED: Assignments can currently only mutate entire locals, not offsets into them, offset: {:?}, old type: {}, target_type: {}, expr_type: {}",
                        derived_from_local.offset, old.data_type, target_type, expr_type
                    )
                    .with_section(|| generate_span_error_section(*span)));
                }
            } else {
                return Err(eyre!(
                    "UNIMPLEMENTED: Assignments only support places that simplify to a pointer deref or are derived from locals",
                )
                .with_section(|| generate_span_error_section(*span)));
            }
        }
        ExpressionOutput::Dereference(target, target_pointer_type, _span) => {
            let target_data_ref = walk_expr(ctx, &*target)?.into_data_ref(ctx)?;

            assert!(
                Type::Pointer(target_type.clone().into())
                    .compatible_with(&target_pointer_type, ctx.type_checker)?
            );

            let width = expr_type.width(ctx.type_checker)?;
            let stride = target_type.stride(ctx.type_checker)?;
            match (width, stride) {
                (0, _) => {}
                (_, Stride::ZST) => unreachable!(),
                (1, Stride::Byte) => {
                    ctx.call_function_like("write8", vec![target_data_ref, expr_data_ref], *span)?
                        .into_data_ref(ctx)?;
                }
                (1, Stride::Native) => {
                    ctx.call_function_like(
                        "write_native",
                        vec![target_data_ref, expr_data_ref],
                        *span,
                    )?
                    .into_data_ref(ctx)?;
                }
                (width, Stride::Byte) => {
                    for idx in 0..width {
                        let char =
                            ctx.reference_relative(Type::Char, &expr_data_ref, Offset(idx))?;

                        let target_char = if idx != 0 {
                            ClacOp::Add {
                                lhs: target_data_ref.clone(),
                                rhs: DataReference::Value(Value::Int(idx as ClacValue), None),
                            }
                            .append_into(ctx)?
                        } else {
                            target_data_ref.clone()
                        };

                        ctx.call_function_like("write8", vec![target_char, char], *span)?
                            .into_data_ref(ctx)?;
                    }
                }
                (width, Stride::Native) => {
                    for idx in 0..width {
                        let int = ctx.reference_relative(Type::Int, &expr_data_ref, Offset(idx))?;

                        let target_int = if idx != 0 {
                            ClacOp::Add {
                                lhs: target_data_ref.clone(),
                                rhs: DataReference::Value(
                                    Value::Int(
                                        idx as ClacValue * (ClacValue::BITS as ClacValue / 8),
                                    ),
                                    None,
                                ),
                            }
                            .append_into(ctx)?
                        } else {
                            target_data_ref.clone()
                        };

                        ctx.call_function_like("write_native", vec![target_int, int], *span)?
                            .into_data_ref(ctx)?;
                    }
                }
            }
        }
    }

    Ok(DataReference::Tempoary(ctx.allocate_tempoary(Type::Void)?, None).into())
}

fn walk_loop<'a, 'b>(ctx: &mut CodegenCtx<'a, 'b>, inner: &Loop<'a>) -> Result<MaybeTailCall<'a>> {
    if let Some(init) = &inner.init {
        walk_local_def(ctx, init)?;
    }

    let loop_call = FunctionCall {
        function: "loop!",
        parameters: Vec::default(),
        span: inner.span,
    };

    let mut block = inner.body.clone();

    if let Some(update) = inner.update.clone() {
        block.statements.push(Statement::Assignment(update));
    }

    block.statements.push(Statement::Expr(
        Expr::FunctionCall(loop_call),
        Punctuation::Unpunctuated,
    ));

    if let Some(cond) = inner.cond.clone() {
        let loop_body = block;

        block = Block {
            statements: vec![Statement::Expr(
                Expr::If(IfExpr {
                    cases: vec![IfCase {
                        condition: cond,
                        span: loop_body.span,
                        contents: loop_body,
                    }],
                    otherwise: None,
                    captures: inner.captures.clone(),
                    return_type: DeferedType::ResolvedType(Type::Void),
                    span: inner.span,
                }),
                Punctuation::Unpunctuated,
            )],
            captures: inner.captures.clone(),
            span: inner.span,
        };
    }

    walk_function_def(
        ctx,
        &FunctionDef {
            attributes: Default::default(),
            function: "loop!",
            contents: block,
            span: inner.span,
            signature: FunctionSignature {
                arguements: Vec::default(),
                captures: inner.captures.clone(),
                return_type: Type::Void,
            },
        },
    )?;
    walk_function_call(
        ctx,
        &FunctionCall {
            function: "loop!",
            parameters: Vec::default(),
            span: inner.span,
        },
    )
}

fn walk_if_expr<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    if_expr: &IfExpr<'a>,
) -> Result<MaybeTailCall<'a>> {
    let IfExpr {
        cases,
        otherwise,
        captures,
        return_type,
        span,
    } = if_expr;

    if otherwise.is_none() && !return_type.compatible_with(&Type::Void, ctx.type_checker)? {
        return Err(eyre!(
            "Got non exhustive if statement with non void return type ({:?})",
            return_type
        )
        .with_section(|| generate_span_error_section(*span)));
    }

    let sig = FunctionSignature {
        arguements: Vec::default(),
        captures: captures.clone(),
        return_type: return_type.clone().unwrap(),
    };

    trace!("if signature: {sig:?}");

    walk_if_statement_inner(ctx, &cases, otherwise.as_ref(), sig)
}

fn walk_if_statement_inner<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    if_cases: &[IfCase<'a>],
    otherwise: Option<&Block<'a>>,
    mut signature: FunctionSignature<'a>,
) -> Result<MaybeTailCall<'a>> {
    if let Some((next_case, remaining)) = if_cases.split_first() {
        let condition = walk_expr(ctx, &next_case.condition)
            .wrap_err("If cond should return something")
            .with_section(|| generate_span_error_section(next_case.span))?
            .into_data_ref(ctx)?;

        let on_true =
            ctx.define_function("on_true!", signature.clone(), &Default::default(), |ctx| {
                walk_block(ctx, &next_case.contents)
            })?;

        let on_false = if !remaining.is_empty() || otherwise.is_some() {
            Some(ctx.define_function(
                "on_false!",
                signature.clone(),
                &Default::default(),
                |ctx| walk_if_statement_inner(ctx, remaining, otherwise, signature.clone()),
            )?)
        } else {
            None
        };

        let clac_op = ClacOp::If {
            condition: condition.clone(),
            on_true,
            on_false,
        };

        let mut tokens = ClacProgram::default();
        clac_op.execute((&mut tokens, &mut *ctx))?;

        let mut parameters = Vec::new();
        for (arg_data_type, _arg_ident, version) in &signature.arguements {
            let DeferedVersion::ResolvedVersion(version) = version else {
                return Err(eyre!("COMPILER BUG: defered version was not resolved"));
            };

            let AnnotatedDataRef {
                reference,
                data_type,
            } = ctx.lookup_local(&version).wrap_err(
                "Look up local for capture for if statement could not find corosponding local",
            )?;

            if !arg_data_type.compatible_with(&data_type, ctx.type_checker)? {
                return Err(eyre!(
                    "Look up local for capture for if statement failed due to type mismatch, arg_data_type: {arg_data_type}, data_type: {data_type}"
                ));
            }

            parameters.push(reference);
        }

        signature.arguements.push((
            Type::Bool,
            "condition",
            DeferedVersion::ResolvedVersion(ctx.type_checker.allocate_version()),
        ));
        parameters.push(condition);

        Ok(MaybeTailCall::TailCall {
            signature: signature,
            call_span: next_case.span,
            parameters,
            tokens: tokens.0,
        })
    } else if let Some(otherwise) = otherwise {
        walk_block(ctx, otherwise)
    } else {
        Ok(DataReference::Tempoary(ctx.allocate_tempoary(Type::Void)?, None).into())
    }
}

#[derive(Debug)]
enum ExpressionOutput<'a> {
    TailCall(MaybeTailCall<'a>),
    Dereference(Box<Expr<'a>>, Type<'a>, Span<'a>),
}

impl<'a> From<DataReference<'a>> for ExpressionOutput<'a> {
    fn from(value: DataReference<'a>) -> Self {
        Self::TailCall(value.into())
    }
}

impl<'a> From<MaybeTailCall<'a>> for ExpressionOutput<'a> {
    fn from(value: MaybeTailCall<'a>) -> Self {
        Self::TailCall(value)
    }
}

impl<'a> ExpressionOutput<'a> {
    fn into_data_ref(self, ctx: &mut CodegenCtx<'a, '_>) -> Result<DataReference<'a>> {
        self.into_tail_call(ctx)?.into_data_ref(ctx)
    }

    // FIXME: this impl is hella cooked

    fn into_tail_call(self, ctx: &mut CodegenCtx<'a, '_>) -> Result<MaybeTailCall<'a>> {
        match self {
            ExpressionOutput::TailCall(tail_call) => Ok(tail_call),
            ExpressionOutput::Dereference(operand, operand_type, _span) => {
                let value = walk_expr(ctx, &operand)?;

                // TODO: make this support the MaybeTailCall infra so that it wont get compiled
                // if it is never used.
                let deref_type = operand_type.dereference(ctx.type_checker)?;
                let width = deref_type.width(ctx.type_checker)?;
                let stride = deref_type.stride(ctx.type_checker)?;
                match (width, stride) {
                    (0, _) => {}
                    (_, Stride::ZST) => unreachable!(),
                    (1, Stride::Byte) => {
                        let target_data_ref = value.into_data_ref(ctx)?;

                        ctx.bring_up_references(&[target_data_ref], 1)?;
                        ctx.push_token(ClacToken::Read8)?;
                    }
                    (1, Stride::Native) => {
                        let target_data_ref = value.into_data_ref(ctx)?;

                        ctx.bring_up_references(&[target_data_ref], 1)?;
                        ctx.push_token(ClacToken::ReadNative)?;
                    }
                    (width, Stride::Byte) => {
                        let target_data_ref = value.into_data_ref(ctx)?;

                        for idx in 0..width {
                            if idx != 0 {
                                let data_ref = ClacOp::Add {
                                    lhs: target_data_ref.clone(),
                                    rhs: DataReference::Value(Value::Int(idx as ClacValue), None),
                                }
                                .append_into(ctx)?;

                                // If the add is performed at run time it will already be at the
                                // top of the stack, but if it was done at compile time, we need to
                                // bring it up
                                match data_ref {
                                    DataReference::Value(_, _) => {
                                        ctx.bring_up_references([&target_data_ref], 1)?;
                                    }
                                    _ => {}
                                }
                            } else {
                                ctx.bring_up_references([&target_data_ref], 1)?;
                            };

                            ctx.push_token(ClacToken::Read8)?;
                        }
                    }
                    (width, Stride::Native) => {
                        let target_data_ref = value.into_data_ref(ctx)?;

                        for idx in 0..width {
                            if idx != 0 {
                                let data_ref = ClacOp::Add {
                                    lhs: target_data_ref.clone(),
                                    rhs: DataReference::Value(
                                        Value::Int(
                                            idx as ClacValue * (ClacValue::BITS as ClacValue / 8),
                                        ),
                                        None,
                                    ),
                                }
                                .append_into(ctx)?;

                                // If the add is performed at run time it will already be at the
                                // top of the stack, but if it was done at compile time, we need to
                                // bring it up
                                match data_ref {
                                    DataReference::Value(_, _) => {
                                        ctx.bring_up_references([&target_data_ref], 1)?;
                                    }
                                    _ => {}
                                }
                            } else {
                                ctx.bring_up_references([&target_data_ref], 1)?;
                            };

                            ctx.push_token(ClacToken::ReadNative)?;
                        }
                    }
                }

                return Ok(
                    DataReference::Tempoary(ctx.allocate_tempoary(deref_type)?, None).into(),
                );
            }
        }
    }
}

fn walk_expr<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    expr: &Expr<'a>,
) -> Result<ExpressionOutput<'a>> {
    match expr {
        Expr::SizeOfType(inner_type, mode, span) => {
            let scale = match mode {
                SizeOfMode::Native => ClacValue::BITS as ClacValue / 8,
                SizeOfMode::Packed => match inner_type.resolve_once(ctx.type_checker)? {
                    Type::Array(inner_type, _) => match inner_type.stride(ctx.type_checker)? {
                        Stride::Native => ClacValue::BITS as ClacValue / 8,
                        Stride::Byte => 1,
                        Stride::ZST => 0,
                    },
                    _ => {
                        return Err(eyre!(
                            "Call to sizeof_packed on a type that does not have a packed repersentation"
                        ).with_section(|| generate_span_error_section(*span)));
                    }
                },
            };

            Ok(DataReference::Value(
                Value::Int(inner_type.width(ctx.type_checker)? * scale),
                None,
            )
            .into())
        }
        Expr::SizeOfExpr(_inner_expr, defered_type, mode, span) => {
            let DeferedType::ResolvedType(inner_type) = defered_type else {
                return Err(eyre!("COMPILER BUG: defered type was not resolved"));
            };

            let scale = match mode {
                SizeOfMode::Native => ClacValue::BITS as ClacValue / 8,
                SizeOfMode::Packed => match inner_type.resolve_once(ctx.type_checker)? {
                    Type::Array(inner_type, _) => match inner_type.stride(ctx.type_checker)? {
                        Stride::Native => ClacValue::BITS as ClacValue / 8,
                        Stride::Byte => 1,
                        Stride::ZST => 0,
                    },
                    _ => {
                        return Err(eyre!(
                            "Call to sizeof_packed on a type that does not have a packed repersentation"
                        ).with_section(|| generate_span_error_section(*span)));
                    }
                },
            };

            Ok(DataReference::Value(
                Value::Int(inner_type.width(ctx.type_checker)? * scale),
                None,
            )
            .into())
        }
        Expr::Value(value, _span) => Ok(DataReference::Value(value.clone(), None).into()),
        Expr::Variable(ident, version, span) => {
            let DeferedVersion::ResolvedVersion(version) = version else {
                return Err(eyre!("COMPILER BUG: defered version was not resolved"));
            };

            Ok(ctx
                .lookup_ident(version)
                .map(|it| it.reference)
                .wrap_err_with(|| format!("Could not find identifier: {ident:?}"))
                .with_section(|| generate_span_error_section(*span))?
                .into())
        }
        Expr::Struct(map, struct_type, _span) => {
            let DeferedType::ResolvedType(struct_type) = struct_type else {
                return Err(eyre!("COMPILER BUG: defered type was not resolved"));
            };

            let data_refs = map
                .iter()
                .map(|(key, expr)| Ok((key, walk_expr(ctx, expr)?.into_data_ref(ctx)?)))
                .collect::<Result<Vec<_>>>()?;

            let maybe_value = data_refs
                .iter()
                .map(
                    |(key, data_ref)| match ctx.dereference_data_ref(data_ref)? {
                        DataReference::Value(value, _) => Ok(Some((&***key, value))),
                        DataReference::Tempoary(_, _) => Ok(None),
                        _ => unreachable!(),
                    },
                )
                .collect::<Result<Option<BTreeMap<_, _>>>>()?;

            if let Some(map) = maybe_value {
                Ok(DataReference::Value(Value::Struct(map), None).into())
            } else {
                let expected_width = struct_type.width(ctx.type_checker)?;
                ctx.bring_up_references(
                    &data_refs
                        .into_iter()
                        .map(|(_, data_ref)| data_ref)
                        .collect::<Vec<_>>(),
                    expected_width,
                )?;

                Ok(
                    DataReference::Tempoary(ctx.allocate_tempoary(struct_type.clone())?, None)
                        .into(),
                )
            }
        }
        Expr::Array(exprs, array_type, _span) => {
            let DeferedType::ResolvedType(array_type @ Type::Array(inner_type, len)) = array_type
            else {
                // TODO: I think empty arrays will hit this
                return Err(eyre!("COMPILER BUG: defered type was not resolved"));
            };

            assert_eq!(exprs.len(), *len as _);

            let data_refs = exprs
                .iter()
                .map(|expr| walk_expr(ctx, expr)?.into_data_ref(ctx))
                .collect::<Result<Vec<_>>>()?;

            let maybe_value = data_refs
                .iter()
                .map(|data_ref| match ctx.dereference_data_ref(data_ref)? {
                    DataReference::Value(value, _) => Ok(Some(value)),
                    DataReference::Tempoary(_, _) => Ok(None),
                    _ => unreachable!(),
                })
                .collect::<Result<Option<Vec<_>>>>()?;

            if let Some(array) = maybe_value {
                Ok(DataReference::Value(Value::Array((**inner_type).clone(), array), None).into())
            } else {
                let expected_width = array_type.width(ctx.type_checker)?;
                ctx.bring_up_references(&data_refs, expected_width)?;

                Ok(
                    DataReference::Tempoary(ctx.allocate_tempoary(array_type.clone())?, None)
                        .into(),
                )
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
            let DeferedType::ResolvedType(left_type) = left_type else {
                return Err(eyre!("COMPILER BUG: defered type was not resolved"));
            };
            let DeferedType::ResolvedType(right_type) = right_type else {
                return Err(eyre!("COMPILER BUG: defered type was not resolved"));
            };

            let lhs = walk_expr(ctx, left)?.into_data_ref(ctx)?;
            let rhs = walk_expr(ctx, right)?.into_data_ref(ctx)?;

            // Scale rhs to have correct semantics for pointer arithmetic
            let (lhs, rhs) = match (
                op,
                left_type.resolve_once(ctx.type_checker)?,
                right_type.resolve_once(ctx.type_checker)?,
            ) {
                (BinaryOp::Add | BinaryOp::Sub, Type::Pointer(inner_type), Type::Int) => {
                    let width = inner_type.width(ctx.type_checker)?;
                    let stride = inner_type.stride(ctx.type_checker)?;

                    match (width, stride) {
                        (0, _) | (_, Stride::ZST) => todo!(),
                        (1, Stride::Byte) => (lhs, rhs),
                        (1, Stride::Native) => {
                            let rhs = ClacOp::Mul {
                                lhs: DataReference::Value(
                                    Value::Int(ClacValue::BITS as ClacValue / 8),
                                    None,
                                ),
                                rhs,
                            }
                            .append_into(ctx)?;

                            (lhs, rhs)
                        }
                        (width, Stride::Byte) => {
                            let rhs = ClacOp::Mul {
                                lhs: DataReference::Value(Value::Int(width), None),
                                rhs,
                            }
                            .append_into(ctx)?;

                            (lhs, rhs)
                        }
                        (width, Stride::Native) => {
                            let rhs = ClacOp::Mul {
                                lhs: DataReference::Value(
                                    Value::Int(ClacValue::BITS as ClacValue / 8 * width),
                                    None,
                                ),
                                rhs,
                            }
                            .append_into(ctx)?;

                            (lhs, rhs)
                        }
                    }
                }
                _ => (lhs, rhs),
            };

            let clac_op = match op {
                BinaryOp::Add => ClacOp::Add { lhs, rhs },
                BinaryOp::Sub => ClacOp::Sub { lhs, rhs },
                BinaryOp::Mul => ClacOp::Mul { lhs, rhs },
                BinaryOp::Div => ClacOp::Div { lhs, rhs },
                BinaryOp::Mod => ClacOp::Mod { lhs, rhs },
                BinaryOp::Pow => ClacOp::Pow { lhs, rhs },
                BinaryOp::Eq => ClacOp::Eq { lhs, rhs },
                BinaryOp::Ne => ClacOp::Ne { lhs, rhs },
                BinaryOp::Le => ClacOp::Le { lhs, rhs },
                BinaryOp::Ge => ClacOp::Ge { lhs, rhs },
                BinaryOp::Lt => ClacOp::Lt { lhs, rhs },
                BinaryOp::Gt => ClacOp::Gt { lhs, rhs },
                BinaryOp::LAnd => ClacOp::LAnd { lhs, rhs },
                BinaryOp::LOr => ClacOp::LOr { lhs, rhs },
                BinaryOp::BShl => ClacOp::BShl { lhs, rhs },
                BinaryOp::BShr => ClacOp::BShr { lhs, rhs },
                BinaryOp::BAnd => ClacOp::BAnd { lhs, rhs },
            };

            let ret = clac_op
                .append_into(ctx)
                .wrap_err_with(|| format!("Append op code '{op:?}' failed"))
                .with_section(|| generate_span_error_section(*span))?;

            // Scale ret to have correct semantics for pointer arithmetic
            let ret = match (
                op,
                left_type.resolve_once(ctx.type_checker)?,
                right_type.resolve_once(ctx.type_checker)?,
            ) {
                (BinaryOp::Sub, Type::Pointer(inner_type), Type::Pointer(_)) => {
                    let width = inner_type.width(ctx.type_checker)?;
                    let stride = inner_type.stride(ctx.type_checker)?;

                    match (width, stride) {
                        (0, _) | (_, Stride::ZST) => todo!(),
                        (1, Stride::Byte) => ret,
                        (1, Stride::Native) => {
                            let ret = ClacOp::Div {
                                lhs: DataReference::Value(
                                    Value::Int(ClacValue::BITS as ClacValue / 8),
                                    None,
                                ),
                                rhs: ret,
                            }
                            .append_into(ctx)?;

                            ret
                        }
                        (width, Stride::Byte) => {
                            let ret = ClacOp::Div {
                                lhs: DataReference::Value(Value::Int(width), None),
                                rhs: ret,
                            }
                            .append_into(ctx)?;

                            ret
                        }
                        (width, Stride::Native) => {
                            let ret = ClacOp::Div {
                                lhs: DataReference::Value(
                                    Value::Int(ClacValue::BITS as ClacValue / 8 * width),
                                    None,
                                ),
                                rhs: ret,
                            }
                            .append_into(ctx)?;

                            ret
                        }
                    }
                }
                _ => ret,
            };

            Ok(ret.into())
        }
        Expr::PrefixOp {
            op,
            operand,
            span,
            operand_type,
        } => {
            let clac_op = match op {
                PrefixOp::Negate => {
                    let value = walk_expr(ctx, operand)?;

                    ClacOp::Neg {
                        value: value.into_data_ref(ctx)?,
                    }
                }
                PrefixOp::LNot => {
                    let value = walk_expr(ctx, operand)?;

                    ClacOp::Not {
                        value: value.into_data_ref(ctx)?,
                    }
                }
                PrefixOp::Cast(to) => {
                    let value = walk_expr(ctx, operand)?;

                    // return match value {
                    //     ExpressionOutput::TailCall(MaybeTailCall::Regular(ref data_reference)) => {
                    //         match ctx.dereference_data_ref(data_reference)? {
                    //             DataReference::Value(value) => {
                    //                 Ok(DataReference::Value(Value::Cast(to.clone(), value.into()))
                    //                     .into())
                    //             }
                    //             _ => Ok(value),
                    //         }
                    //     }
                    //     tail_call @ ExpressionOutput::TailCall(MaybeTailCall::TailCall {
                    //         ..
                    //     }) => Ok(tail_call),
                    //     ExpressionOutput::Dereference(expr, _expr_type, span) => {
                    //         Ok(ExpressionOutput::Dereference(
                    //             expr,
                    //             Type::Pointer(to.clone().into()),
                    //             span,
                    //         ))
                    //     }
                    // };

                    return match value.into_tail_call(ctx)? {
                        MaybeTailCall::Regular(ref data_reference) => {
                            match ctx.dereference_data_ref(data_reference)? {
                                DataReference::Value(value, derived_from) => {
                                    Ok(DataReference::Value(
                                        Value::Cast(to.clone(), value.into()),
                                        derived_from,
                                    )
                                    .into())
                                }
                                value => Ok(value.into()),
                            }
                        }
                        tail_call @ MaybeTailCall::TailCall { .. } => Ok(tail_call.into()),
                    };
                }
                PrefixOp::Dereference => {
                    let DeferedType::ResolvedType(operand_type) = operand_type else {
                        return Err(eyre!("COMPILER BUG: defered type was not resolved"));
                    };

                    return Ok(ExpressionOutput::Dereference(
                        operand.clone(),
                        operand_type.clone(),
                        span.clone(),
                    ));
                }
                PrefixOp::AddressOf => {
                    let place = walk_expr(ctx, operand)?;

                    let ExpressionOutput::Dereference(target, target_pointer_type, _span) = place
                    else {
                        return Err(eyre!(
                            "UNIMPLEMENTED: AddressOf only support places that simplify to a pointer deref",
                        )
                        .with_section(|| generate_span_error_section(*span)));
                    };

                    let DeferedType::ResolvedType(operand_type) = operand_type else {
                        return Err(eyre!("COMPILER BUG: defered type was not resolved"));
                    };
                    assert!(
                        Type::Pointer(operand_type.clone().into())
                            .compatible_with(&target_pointer_type, ctx.type_checker)?
                    );

                    return walk_expr(ctx, &target);
                }
            };

            let ret = clac_op
                .append_into(ctx)
                .wrap_err_with(|| format!("Append op code '{op:?}' failed"))
                .with_section(|| generate_span_error_section(*span))?;
            Ok(ret.into())
        }
        Expr::PostfixOp {
            op,
            operand,
            span,
            operand_type,
        } => {
            let DeferedType::ResolvedType(operand_type) = operand_type else {
                return Err(eyre!("COMPILER BUG: defered type was not resolved"));
            };

            match (operand_type.resolve_once(ctx.type_checker)?, op) {
                (Type::Struct(_), PostfixOp::Member(ident)) => {
                    let (field_type, field_offset) =
                        operand_type.member_and_offset(ctx.type_checker, ident)?;

                    let value = walk_expr(ctx, operand)?;
                    match value {
                        ExpressionOutput::TailCall(maybe_tail_call) => {
                            let data_ref = maybe_tail_call.into_data_ref(ctx)?;

                            Ok(ctx
                                .reference_relative(field_type, &data_ref, field_offset)?
                                .into())
                        }
                        ExpressionOutput::Dereference(expr, expr_type, span) => walk_expr(
                            ctx,
                            &Expr::PostfixOp {
                                op: PostfixOp::MemberDeref(ident),
                                operand: expr,
                                operand_type: DeferedType::ResolvedType(expr_type),
                                span,
                            },
                        ),
                    }
                }
                (Type::Pointer(inner), PostfixOp::MemberDeref(ident)) => {
                    let (field_type, field_offset) =
                        inner.member_and_offset(ctx.type_checker, ident)?;

                    assert!(field_type.stride(ctx.type_checker)? == Stride::Native);

                    // Try to help out value propagation
                    let offset = match ((**operand).clone(), field_offset) {
                        (operand, Offset(0)) => operand,
                        // (
                        //     Expr::BinaryOp {
                        //         op: BinaryOp::Add,
                        //         left,
                        //         left_type,
                        //         right,
                        //         right_type,
                        //         span,
                        //     },
                        //     _,
                        // ) => {
                        //     assert_eq!(right_type, DeferedType::ResolvedType(Type::Int));
                        //
                        //     Expr::BinaryOp {
                        //         op: BinaryOp::Add,
                        //         left,
                        //         left_type,
                        //         right: Expr::BinaryOp {
                        //             op: BinaryOp::Add,
                        //             left: right,
                        //             left_type: right_type,
                        //             right: Expr::Value(Value::Int(field_offset.0), span).into(),
                        //             right_type: DeferedType::ResolvedType(Type::Int),
                        //             span,
                        //         }
                        //         .into(),
                        //         right_type: DeferedType::ResolvedType(Type::Int),
                        //         span,
                        //     }
                        // }
                        _ => Expr::BinaryOp {
                            op: BinaryOp::Add,
                            left: operand.clone(),
                            left_type: DeferedType::ResolvedType(Type::Pointer(Type::Int.into())),
                            right: Expr::Value(Value::Int(field_offset.0), *span).into(),
                            right_type: DeferedType::ResolvedType(Type::Int),
                            span: *span,
                        },
                    };

                    walk_expr(
                        ctx,
                        &Expr::PrefixOp {
                            op: PrefixOp::Dereference,
                            operand: offset.into(),
                            operand_type: DeferedType::ResolvedType(Type::Pointer(
                                field_type.into(),
                            )),
                            span: *span,
                        },
                    )
                }
                (Type::Array(inner_type, len), PostfixOp::ArrayIndex(idx_expr)) => {
                    let value = walk_expr(ctx, operand)?;

                    match value {
                        ExpressionOutput::TailCall(maybe_tail_call) => {
                            let field_width = inner_type.width(ctx.type_checker)?;
                            let data_ref = maybe_tail_call.into_data_ref(ctx)?;
                            let idx = walk_expr(ctx, idx_expr)?;

                            let ExpressionOutput::TailCall(MaybeTailCall::Regular(
                                DataReference::Value(Value::Int(idx), _),
                            )) = idx
                            else {
                                return Err(eyre!(
                                    "UNIMPLEMENTED: Can not index into a stack array with a index that is not known at compile time"
                                ));
                            };

                            assert!(len >= 0);
                            if idx < 0 || idx >= len {
                                return Err(eyre!("Array Index out of bounds").with_section(|| {
                                generate_span_error_section_with_annotations(
                                    *span,
                                    &[
                                        (idx_expr.as_span(), &format!("This index is computed to be {idx}, but the length is only {len}"))
                                    ])
                                }));
                            }

                            Ok(ctx
                                .reference_relative(
                                    *inner_type,
                                    &data_ref,
                                    Offset(field_width * idx),
                                )?
                                .into())
                        }
                        ExpressionOutput::Dereference(expr, _expr_type, span) => {
                            // TODO: Do a similar value propagation optimization as the other cases
                            // TODO: Dont omit an add when the index is a comptime 0
                            // TODO: when index is comptime known, do bounds checking

                            walk_expr(
                                ctx,
                                &Expr::PrefixOp {
                                    op: PrefixOp::Dereference,
                                    operand: Expr::BinaryOp {
                                        op: BinaryOp::Add,
                                        left: expr.clone(),
                                        left_type: DeferedType::ResolvedType(Type::Pointer(
                                            inner_type.clone(),
                                        )),
                                        right: idx_expr.clone(),
                                        right_type: DeferedType::ResolvedType(Type::Int),
                                        span,
                                    }
                                    .into(),
                                    operand_type: DeferedType::ResolvedType(Type::Pointer(
                                        inner_type.clone(),
                                    )),
                                    span,
                                },
                            )
                        }
                    }
                }
                (Type::Pointer(inner), PostfixOp::ArrayIndex(expr)) => {
                    let offset = match (**operand).clone() {
                        // Try to help out value propagation
                        // Expr::BinaryOp {
                        //     op: BinaryOp::Add,
                        //     left,
                        //     left_type,
                        //     right,
                        //     right_type,
                        //     span,
                        // } => {
                        //     assert_eq!(right_type, DeferedType::ResolvedType(Type::Int));
                        //
                        //     Expr::BinaryOp {
                        //         op: BinaryOp::Add,
                        //         left,
                        //         left_type,
                        //         right: Expr::BinaryOp {
                        //             op: BinaryOp::Add,
                        //             left: right,
                        //             left_type: right_type,
                        //             right: expr.clone(),
                        //             right_type: DeferedType::ResolvedType(Type::Int),
                        //             span,
                        //         }
                        //         .into(),
                        //         right_type: DeferedType::ResolvedType(Type::Int),
                        //         span,
                        //     }
                        // }
                        _ => Expr::BinaryOp {
                            op: BinaryOp::Add,
                            left: operand.clone(),
                            left_type: DeferedType::ResolvedType(operand_type.clone()),
                            right: expr.clone(),
                            right_type: DeferedType::ResolvedType(Type::Int),
                            span: *span,
                        },
                    };

                    walk_expr(
                        ctx,
                        &Expr::PrefixOp {
                            op: PrefixOp::Dereference,
                            operand: offset.into(),
                            operand_type: DeferedType::ResolvedType(Type::Pointer(inner.clone())),
                            span: *span,
                        },
                    )
                }
                _ => unreachable!(),
            }
        }
        Expr::FunctionCall(func_call) => Ok(walk_function_call(ctx, func_call)?.into()),
        Expr::If(if_expr) => Ok(walk_if_expr(ctx, if_expr)?.into()),
    }
}

pub fn generate_span_error_section(span: Span) -> String {
    generate_span_error_section_with_annotations(span, &[])
}

pub fn generate_span_error_section_with_annotations(
    span: Span,
    annotations: &[(Span, &str)],
) -> String {
    let mut string = String::new();
    for line_span in span.lines_span() {
        let (line, _col) = line_span.start_pos().line_col();
        write!(&mut string, "{line:4} | {}", line_span.as_str()).unwrap();

        for (anno_span, annotation) in annotations {
            for anno_line_span in anno_span.lines_span() {
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
