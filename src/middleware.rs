use anyhow::Context;

use crate::{
    ast::{
        BinaryOp, Block, Expr, FunctionCall, FunctionDef, IfCase, IfStatement, LocalDef, Statement,
        StaticDef,
    },
    codegen::{ClacOp, CodegenCtx, DataReference, FunctionSignature},
};

pub fn walk_block<'a>(ctx: &mut CodegenCtx<'a>, block: &'a Block) -> anyhow::Result<()> {
    for statement in &block.statements {
        match statement {
            Statement::Static(static_def) => walk_static_def(ctx, static_def)?,
            Statement::Local(local_def) => walk_local_def(ctx, local_def)?,
            Statement::Return(expr) => walk_return(ctx, expr)?,
            Statement::If(if_statement) => walk_if_statement(ctx, if_statement)?,
            Statement::FunctionDef(function_def) => walk_function_def(ctx, function_def)?,
            Statement::FunctionCall(function_call) => {
                walk_function_call(ctx, function_call)?;
            }
        }
    }

    Ok(())
}

fn walk_function_call<'a>(
    ctx: &mut CodegenCtx<'a>,
    func_call: &'a FunctionCall,
) -> anyhow::Result<DataReference<'a>> {
    let parameters = func_call
        .paramaters
        .iter()
        .map(|it| walk_expr(ctx, it))
        .collect::<anyhow::Result<Vec<_>>>()?;

    let clac_op = ClacOp::Call {
        name: crate::codegen::DefinitionIdent::Function(&func_call.function),
        parameters,
    };

    let tempoary = clac_op.append_into(ctx).unwrap();
    Ok(DataReference::Tempoary(tempoary))
}

fn walk_function_def<'a>(
    ctx: &mut CodegenCtx<'a>,
    func_def: &'a FunctionDef,
) -> anyhow::Result<()> {
    ctx.define_function(
        &func_def.function,
        FunctionSignature {
            arguements: func_def
                .arguements
                .iter()
                .map(|(var_type, ident)| (*var_type, ident.as_str()))
                .collect(),
            return_type: func_def.return_type,
        },
        |ctx| walk_block(ctx, &func_def.contents),
    )?;

    Ok(())
}

fn walk_static_def<'a>(ctx: &mut CodegenCtx<'a>, static_def: &'a StaticDef) -> anyhow::Result<()> {
    let StaticDef {
        name,
        var_type,
        value,
    } = static_def;

    ctx.define_static(name, *var_type, *value);

    Ok(())
}

fn walk_local_def<'a>(ctx: &mut CodegenCtx<'a>, local_def: &'a LocalDef) -> anyhow::Result<()> {
    let data_ref = walk_expr(ctx, &local_def.expr)?;
    ctx.promote_to_local(data_ref, &local_def.name, local_def.var_type);

    Ok(())
}

fn walk_return<'a>(ctx: &mut CodegenCtx<'a>, expr: &'a Expr) -> anyhow::Result<()> {
    let data_ref = walk_expr(ctx, expr)?;

    // FIXME: This only works for return in ending position
    // todo!("We dont actualy have infra to return yet")

    Ok(())
}

// TODO: Support expresion position if statements
fn walk_if_statement<'a>(
    ctx: &mut CodegenCtx<'a>,
    if_statement: &'a IfStatement,
) -> anyhow::Result<()> {
    walk_if_statement_inner(ctx, &if_statement.cases, if_statement.otherwise.as_ref())
}

fn walk_if_statement_inner<'a>(
    ctx: &mut CodegenCtx<'a>,
    if_cases: &'a [IfCase],
    otherwise: Option<&'a Block>,
) -> anyhow::Result<()> {
    if let Some((next_case, remaining)) = if_cases.split_first() {
        let condition =
            walk_expr(ctx, &next_case.condition).expect("If cond should return something");

        let on_true = ctx.define_function("on_true", FunctionSignature::default(), |ctx| {
            walk_block(ctx, &next_case.contents)
        })?;

        let on_false = if !remaining.is_empty() || otherwise.is_some() {
            Some(
                ctx.define_function("on_false", FunctionSignature::default(), |ctx| {
                    walk_if_statement_inner(ctx, remaining, otherwise)
                })?,
            )
        } else {
            None
        };

        let clac_op = ClacOp::If {
            condition,
            on_true,
            on_false,
        };
        clac_op.append_into(ctx);

        Ok(())
    } else if let Some(otherwise) = otherwise {
        walk_block(ctx, &otherwise)
    } else {
        Ok(())
    }
}

fn walk_expr<'a>(ctx: &mut CodegenCtx<'a>, expr: &'a Expr) -> anyhow::Result<DataReference<'a>> {
    match expr {
        // TODO: Do we need to handle bools seperatly?
        Expr::Value(value) => Ok(DataReference::Number(value.as_repr())),
        Expr::Ident(ident) => ctx.lookup_ident_data_ref(ident).context("Got bad ident"),
        Expr::BinaryOp { op, left, right } => {
            let lhs = walk_expr(ctx, left)?;
            let rhs = walk_expr(ctx, right)?;

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
            };

            let tempoary = clac_op.append_into(ctx).unwrap();
            Ok(DataReference::Tempoary(tempoary))
        }
        Expr::UnaryOp { op, operand } => {
            let value = walk_expr(ctx, operand)?;

            let clac_op = match op {
                crate::ast::UnaryOp::Negate => ClacOp::Neg { value },
                crate::ast::UnaryOp::LNot => ClacOp::Not { value },
            };

            let tempoary = clac_op.append_into(ctx).unwrap();
            Ok(DataReference::Tempoary(tempoary))
        }
        Expr::FunctionCall(func_call) => walk_function_call(ctx, func_call),
    }
}
