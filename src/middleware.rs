use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Result, eyre},
};
use pest::Span;
use std::{fmt::Write, sync::Arc};
use tracing::{instrument, trace};

use crate::{
    ast::{
        BinaryOp, Block, ConstDef, DeferedType, Expr, FunctionCall, FunctionDef, IfCase, IfExpr,
        LocalDef, Punctuation, Statement, Type,
    },
    codegen::{
        AnnotatedDataRef, CodegenCtx, MaybeTailCall,
        clac::ClacProgram,
        ir::{ClacOp, DataReference, FunctionSignature},
    },
};

#[instrument(skip(ctx), fields(%block))]
pub fn walk_block<'a>(ctx: &mut CodegenCtx<'a>, block: &'a Block<'a>) -> Result<MaybeTailCall<'a>> {
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
        }
    }

    if let Some(last_return_val) = last_return_val {
        Ok(last_return_val)
    } else {
        Ok(DataReference::Tempoary(ctx.allocate_tempoary(Type::Void)).into())
    }
}

#[instrument(skip(ctx), fields(%func_call))]
fn walk_function_call<'a>(
    ctx: &mut CodegenCtx<'a>,
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
fn walk_function_def<'a>(ctx: &mut CodegenCtx<'a>, func_def: &'a FunctionDef) -> Result<()> {
    ctx.define_function(
        func_def.function,
        FunctionSignature {
            arguements: func_def
                .arguements
                .iter()
                .map(|(var_type, ident)| (*var_type, *ident))
                .collect(),
            return_type: func_def.return_type,
        },
        &func_def.attributes,
        move |ctx| walk_block(ctx, &func_def.contents),
    )
    .wrap_err_with(|| format!("Walk function def '{:?}' failed", func_def.function))
    .with_section(|| generate_span_error_section(func_def.span))?;

    Ok(())
}

#[instrument(skip(ctx), fields(%const_def))]
fn walk_const_def<'a>(ctx: &mut CodegenCtx<'a>, const_def: &'a ConstDef) -> Result<()> {
    let ConstDef {
        name,
        var_type,
        value,
        ..
    } = const_def;

    ctx.define_const(name, *var_type, *value)?;

    Ok(())
}

#[instrument(skip(ctx), fields(%local_def))]
fn walk_local_def<'a>(ctx: &mut CodegenCtx<'a>, local_def: &'a LocalDef) -> Result<()> {
    let data_ref = walk_expr(ctx, &local_def.expr)?.into_data_ref(ctx)?;
    ctx.promote_to_local(data_ref, local_def.name, local_def.var_type);

    Ok(())
}

#[instrument(skip(ctx), fields(%if_expr))]
fn walk_if_expr<'a>(ctx: &mut CodegenCtx<'a>, if_expr: &'a IfExpr) -> Result<MaybeTailCall<'a>> {
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
            .map(|(a, b)| (*b, *a))
            .collect(),
        return_type: if_expr.return_type.unwrap(),
    };

    trace!("if signature: {sig:?}");

    walk_if_statement_inner(ctx, &if_expr.cases, if_expr.otherwise.as_ref(), sig)
}

#[instrument(skip_all)]
fn walk_if_statement_inner<'a>(
    ctx: &mut CodegenCtx<'a>,
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
            condition,
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
        Ok(DataReference::Tempoary(ctx.allocate_tempoary(Type::Void)).into())
    }
}

#[instrument(skip(ctx), fields(%expr))]
fn walk_expr<'a>(ctx: &mut CodegenCtx<'a>, expr: &'a Expr) -> Result<MaybeTailCall<'a>> {
    match expr {
        Expr::Value(value, _span) => Ok(DataReference::Number(value.as_repr()).into()),
        Expr::Ident(ident, span) => Ok(ctx
            .lookup_ident_data_ref(ident)
            .map(|it| it.reference)
            .wrap_err_with(|| format!("Could not find identifier: {ident}"))
            .with_section(|| generate_span_error_section(*span))?
            .into()),
        Expr::BinaryOp {
            op,
            left,
            right,
            span,
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

            let tempoary = clac_op
                .append_into(ctx)
                .wrap_err_with(|| format!("Append op code '{op:?}' failed"))
                .with_section(|| generate_span_error_section(*span))?;
            Ok(DataReference::Tempoary(tempoary).into())
        }
        Expr::UnaryOp { op, operand, span } => {
            let value = walk_expr(ctx, operand)?.into_data_ref(ctx)?;

            let clac_op = match op {
                crate::ast::UnaryOp::Negate => ClacOp::Neg { value },
                crate::ast::UnaryOp::LNot => ClacOp::Not { value },
            };

            let tempoary = clac_op
                .append_into(ctx)
                .wrap_err_with(|| format!("Append op code '{op:?}' failed"))
                .with_section(|| generate_span_error_section(*span))?;
            Ok(DataReference::Tempoary(tempoary).into())
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
