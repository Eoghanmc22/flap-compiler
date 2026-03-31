use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Ok, Result, eyre},
};
use pest::Span;
use std::{collections::BTreeMap, fmt::Write, sync::Arc};
use tracing::{instrument, trace};

use crate::{
    ast::{
        AsSpan, BinaryOp, Block, ConstDef, DeferedType, Expr, FunctionCall, FunctionDef,
        FunctionSignature, IfCase, IfExpr, LocalDef, PtrAssign, Punctuation, Statement, Stride,
        Type, UnaryOp, Value,
    },
    codegen::{
        AnnotatedDataRef, CodegenCtx, MaybeTailCall, Offset,
        clac::{ClacProgram, ClacValue},
        ir::{ClacOp, DataReference},
    },
};

#[instrument(skip(ctx), fields(%block))]
pub fn walk_block<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    block: &'a Block<'a>,
) -> Result<MaybeTailCall<'a>> {
    let mut last_return_val = None;

    for statement in &block.statements {
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
            Statement::PtrAssign(ptr_assign) => {
                walk_ptr_assign(ctx, ptr_assign)?.into_data_ref(ctx)?;
                None
            }
            Statement::Typedef(_) => None,
        }
    }

    if let Some(last_return_val) = last_return_val {
        Ok(last_return_val)
    } else {
        Ok(DataReference::Tempoary(ctx.allocate_tempoary(Type::Void)?).into())
    }
}

#[instrument(skip(ctx), fields(%func_call))]
fn walk_function_call<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    func_call: &'a FunctionCall<'a>,
) -> Result<MaybeTailCall<'a>> {
    let parameters = func_call
        .parameters
        .iter()
        .map(|it| walk_expr(ctx, it)?.into_data_ref(ctx))
        .collect::<Result<Vec<DataReference<'a>>>>()?;

    ctx.call_function_like(func_call.function, parameters, func_call.span)
        .wrap_err_with(|| format!("Walk function call '{:?}' failed", func_call.function))
        .with_section(|| generate_span_error_section(func_call.span))
}

#[instrument(skip(ctx), fields(%func_def))]
fn walk_function_def<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    func_def: &'a FunctionDef,
) -> Result<()> {
    ctx.define_function(
        func_def.function,
        func_def.signature.clone(),
        &func_def.attributes,
        move |ctx| walk_block(ctx, &func_def.contents),
    )
    .wrap_err_with(|| format!("Walk function def '{:?}' failed", func_def.function))
    .with_section(|| generate_span_error_section(func_def.span))?;

    Ok(())
}

#[instrument(skip(ctx), fields(%const_def))]
fn walk_const_def<'a, 'b>(ctx: &mut CodegenCtx<'a, 'b>, const_def: &'a ConstDef) -> Result<()> {
    let ConstDef {
        name,
        var_type,
        expr,
        ..
    } = const_def;

    let expr_data_ref = walk_expr(ctx, expr)?.into_data_ref(ctx)?;
    let expr_data_ref = ctx.dereference_data_ref(&expr_data_ref)?;
    let expr_value = match expr_data_ref {
        DataReference::Value(val) => val,
        _ => {
            return Err(eyre!("Const could not be evaluated at compile time"))
                .with_section(|| generate_span_error_section(const_def.as_span()));
        }
    };

    assert_eq!(
        var_type.resolve(ctx.type_checker)?,
        expr_value.compute_type().resolve(ctx.type_checker)?
    );

    ctx.define_const(name, expr_value);

    Ok(())
}

#[instrument(skip(ctx), fields(%local_def))]
fn walk_local_def<'a, 'b>(ctx: &mut CodegenCtx<'a, 'b>, local_def: &'a LocalDef) -> Result<()> {
    let data_ref = walk_expr(ctx, &local_def.expr)?.into_data_ref(ctx)?;
    ctx.promote_to_local(data_ref, local_def.name, local_def.var_type.clone());

    Ok(())
}

#[instrument(skip(ctx), fields(%ptr_assign))]
fn walk_ptr_assign<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    ptr_assign: &'a PtrAssign,
) -> Result<MaybeTailCall<'a>> {
    let expr_data_ref = walk_expr(ctx, &ptr_assign.expr)?.into_data_ref(ctx)?;
    let target_data_ref = walk_expr(ctx, &ptr_assign.target)?.into_data_ref(ctx)?;

    let DeferedType::ResolvedType(target_type) = ptr_assign.target_type.clone() else {
        return Err(eyre!("COMPILER BUG: defered type was not resolved"));
    };

    let DeferedType::ResolvedType(expr_type) = ptr_assign.expr_type.clone() else {
        return Err(eyre!("COMPILER BUG: defered type was not resolved"));
    };

    let width = expr_type.width(ctx.type_checker)?;
    let stride = target_type.stride(ctx.type_checker)?;
    match (width, stride) {
        (0, _) => {}
        (_, Stride::ZST) => unreachable!(),
        (1, Stride::Byte) => {
            ctx.call_function_like(
                "write8",
                vec![target_data_ref, expr_data_ref],
                ptr_assign.span,
            )?
            .into_data_ref(ctx)?;
        }
        (1, Stride::Native) => {
            ctx.call_function_like(
                "write_native",
                vec![target_data_ref, expr_data_ref],
                ptr_assign.span,
            )?
            .into_data_ref(ctx)?;
        }
        (width, Stride::Byte) => {
            for idx in 0..width {
                let char =
                    ctx.reference_relative(Type::Char, expr_data_ref.clone(), Offset(idx))?;

                let target_char = if idx != 0 {
                    ClacOp::Add {
                        lhs: target_data_ref.clone(),
                        rhs: DataReference::Value(Value::Int(idx as ClacValue)),
                    }
                    .append_into(ctx)?
                } else {
                    target_data_ref.clone()
                };

                ctx.call_function_like("write8", vec![target_char, char], ptr_assign.span)?
                    .into_data_ref(ctx)?;
            }
        }
        (width, Stride::Native) => {
            for idx in 0..width {
                let int = ctx.reference_relative(Type::Int, expr_data_ref.clone(), Offset(idx))?;

                let target_int = if idx != 0 {
                    ClacOp::Add {
                        lhs: target_data_ref.clone(),
                        rhs: DataReference::Value(Value::Int(
                            idx as ClacValue * (ClacValue::BITS as ClacValue / 8),
                        )),
                    }
                    .append_into(ctx)?
                } else {
                    target_data_ref.clone()
                };

                ctx.call_function_like("write_native", vec![target_int, int], ptr_assign.span)?
                    .into_data_ref(ctx)?;
            }
        }
    }

    return Ok(DataReference::Tempoary(ctx.allocate_tempoary(Type::Void)?).into());
}

#[instrument(skip(ctx), fields(%if_expr))]
fn walk_if_expr<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    if_expr: &'a IfExpr,
) -> Result<MaybeTailCall<'a>> {
    if if_expr.otherwise.is_none() && if_expr.return_type != DeferedType::ResolvedType(Type::Void) {
        return Err(eyre!(
            "Got non exhustive if statement with non void return type ({:?})",
            if_expr.return_type
        )
        .with_section(|| generate_span_error_section(if_expr.span)));
    }

    let sig = FunctionSignature {
        arguements: if_expr
            .captures
            .unwrap()
            .captures
            .iter()
            .map(|(a, b)| (b.clone(), *a))
            .collect(),
        return_type: if_expr.return_type.clone().unwrap(),
    };

    trace!("if signature: {sig:?}");

    walk_if_statement_inner(ctx, &if_expr.cases, if_expr.otherwise.as_ref(), sig)
}

#[instrument(skip_all)]
fn walk_if_statement_inner<'a, 'b>(
    ctx: &mut CodegenCtx<'a, 'b>,
    if_cases: &'a [IfCase],
    otherwise: Option<&'a Block>,
    mut signature: FunctionSignature<'a>,
) -> Result<MaybeTailCall<'a>> {
    if let Some((next_case, remaining)) = if_cases.split_first() {
        let condition = walk_expr(ctx, &next_case.condition)
            .wrap_err("If cond should return something")
            .with_section(|| generate_span_error_section(next_case.span))?
            .into_data_ref(ctx)?;

        let on_true =
            ctx.define_function("on_true", signature.clone(), &Default::default(), |ctx| {
                walk_block(ctx, &next_case.contents)
            })?;

        let on_false = if !remaining.is_empty() || otherwise.is_some() {
            Some(ctx.define_function(
                "on_false",
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
        for (arg_data_type, arg_ident) in &signature.arguements {
            let AnnotatedDataRef {
                reference,
                data_type,
            } = ctx.lookup_local(arg_ident).wrap_err(
                "Look up local for capture for if statement could not find corosponding local",
            )?;

            if *arg_data_type != data_type {
                return Err(eyre!(
                    "Look up local for capture for if statement failed due to type mismatch"
                ));
            }

            parameters.push(reference);
        }

        signature.arguements.push((Type::Bool, "condition"));
        parameters.push(condition);

        Ok(MaybeTailCall::TailCall {
            signature: Arc::new(signature),
            call_span: next_case.span,
            parameters,
            tokens: Arc::new(tokens.0),
        })
    } else if let Some(otherwise) = otherwise {
        walk_block(ctx, otherwise)
    } else {
        Ok(DataReference::Tempoary(ctx.allocate_tempoary(Type::Void)?).into())
    }
}

#[instrument(skip(ctx), fields(%expr))]
fn walk_expr<'a, 'b>(ctx: &mut CodegenCtx<'a, 'b>, expr: &'a Expr) -> Result<MaybeTailCall<'a>> {
    match expr {
        Expr::Value(value, _span) => Ok(DataReference::Value(value.clone()).into()),
        Expr::Path(ident, span) => Ok(ctx
            .lookup_ident_path(ident)
            .map(|it| it.reference)
            .wrap_err_with(|| format!("Could not find identifier: {ident:?}"))
            .with_section(|| generate_span_error_section(*span))?
            .into()),
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
                        DataReference::Value(value) => Ok(Some((&***key, value))),
                        DataReference::Tempoary(_) => Ok(None),
                        _ => unreachable!(),
                    },
                )
                .collect::<Result<Option<BTreeMap<_, _>>>>()?;

            if let Some(map) = maybe_value {
                Ok(DataReference::Value(Value::Struct(map)).into())
            } else {
                let expected_width = struct_type.width(ctx.type_checker)?;
                ctx.bring_up_references(
                    &data_refs
                        .into_iter()
                        .map(|(_, data_ref)| data_ref)
                        .collect::<Vec<_>>(),
                    expected_width,
                )?;

                Ok(DataReference::Tempoary(ctx.allocate_tempoary(struct_type.clone())?).into())
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
                    DataReference::Value(value) => Ok(Some(value)),
                    DataReference::Tempoary(_) => Ok(None),
                    _ => unreachable!(),
                })
                .collect::<Result<Option<Vec<_>>>>()?;

            if let Some(map) = maybe_value {
                Ok(DataReference::Value(Value::Array((**inner_type).clone(), map)).into())
            } else {
                let expected_width = array_type.width(ctx.type_checker)?;
                ctx.bring_up_references(&data_refs, expected_width)?;

                Ok(DataReference::Tempoary(ctx.allocate_tempoary(array_type.clone())?).into())
            }
        }
        Expr::BinaryOp {
            op,
            left,
            right,
            span,
            left_type: _,
            right_type: _,
        } => {
            let lhs = walk_expr(ctx, left)?.into_data_ref(ctx)?;
            let rhs = walk_expr(ctx, right)?.into_data_ref(ctx)?;

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
            Ok(ret.into())
        }
        Expr::UnaryOp {
            op,
            operand,
            span,
            operand_type,
        } => {
            let value = walk_expr(ctx, operand)?;

            let clac_op = match op {
                UnaryOp::Negate => ClacOp::Neg {
                    value: value.into_data_ref(ctx)?,
                },
                UnaryOp::LNot => ClacOp::Not {
                    value: value.into_data_ref(ctx)?,
                },
                UnaryOp::Cast(to) => {
                    return match &value {
                        MaybeTailCall::Regular(data_reference) => {
                            match ctx.dereference_data_ref(data_reference)? {
                                DataReference::Value(value) => {
                                    Ok(DataReference::Value(Value::Cast(to.clone(), value.into()))
                                        .into())
                                }
                                _ => Ok(value),
                            }
                        }
                        _ => Ok(value),
                    };
                }
                UnaryOp::Dereference => {
                    let DeferedType::ResolvedType(operand_type) = operand_type else {
                        return Err(eyre!("COMPILER BUG: defered type was not resolved"));
                    };

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
                            ctx.call_function_like("read8", vec![target_data_ref], *span)?
                                .into_data_ref(ctx)?;
                        }
                        (1, Stride::Native) => {
                            let target_data_ref = value.into_data_ref(ctx)?;

                            ctx.call_function_like("read_native", vec![target_data_ref], *span)?
                                .into_data_ref(ctx)?;
                        }
                        (width, Stride::Byte) => {
                            let target_data_ref = value.into_data_ref(ctx)?;

                            for idx in 0..width {
                                let target_char = if idx != 0 {
                                    ClacOp::Add {
                                        lhs: target_data_ref.clone(),
                                        rhs: DataReference::Value(Value::Int(idx as ClacValue)),
                                    }
                                    .append_into(ctx)?
                                } else {
                                    target_data_ref.clone()
                                };

                                ctx.call_function_like("read8", vec![target_char], *span)?
                                    .into_data_ref(ctx)?;
                            }
                        }
                        (width, Stride::Native) => {
                            let target_data_ref = value.into_data_ref(ctx)?;

                            for idx in 0..width {
                                let target_int = if idx != 0 {
                                    ClacOp::Add {
                                        lhs: target_data_ref.clone(),
                                        rhs: DataReference::Value(Value::Int(
                                            idx as ClacValue * (ClacValue::BITS as ClacValue / 8),
                                        )),
                                    }
                                    .append_into(ctx)?
                                } else {
                                    target_data_ref.clone()
                                };

                                ctx.call_function_like("read_native", vec![target_int], *span)?
                                    .into_data_ref(ctx)?;
                            }
                        }
                    }

                    return Ok(DataReference::Tempoary(ctx.allocate_tempoary(deref_type)?).into());
                }
            };

            let ret = clac_op
                .append_into(ctx)
                .wrap_err_with(|| format!("Append op code '{op:?}' failed"))
                .with_section(|| generate_span_error_section(*span))?;
            Ok(ret.into())
        }
        Expr::FunctionCall(func_call) => walk_function_call(ctx, func_call),
        Expr::If(if_expr) => walk_if_expr(ctx, if_expr),
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
