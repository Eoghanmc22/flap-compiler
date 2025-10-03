// TODO: Make if statements expresion position, and make expressions statements

use anyhow::{Context, bail};
use pest::{
    Parser,
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
};
use pest_derive::Parser;

use crate::ast::{
    BinaryOp, Block, Expr, FunctionCall, FunctionDef, Ident, IfCase, IfStatement, LocalDef,
    Statement, StaticDef, Type, UnaryOp, Value,
};

lazy_static::lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use Rule::*;
        use Assoc::*;

        PrattParser::new()
            // Lowest precedence first
            .op(Op::infix(logical_or, Left))           // ||
            .op(Op::infix(logical_and, Left))          // &&
            .op(Op::infix(eq, Left) | Op::infix(ne, Left))                    // == !=
            .op(Op::infix(le, Left) | Op::infix(ge, Left) | Op::infix(lt, Left) | Op::infix(gt, Left))  // <= >= < >
            .op(Op::infix(add, Left) | Op::infix(subtract, Left))             // + -
            .op(Op::infix(multiply, Left) | Op::infix(divide, Left) | Op::infix(modulo, Left))  // * / %
            .op(Op::infix(power, Right))               // ^ ** (right-associative)
            // Highest precedence
            .op(Op::prefix(logical_not) | Op::prefix(subtract))               // ! - (unary)
    };
}

#[derive(Parser)]
#[grammar = "flap.pest"]
struct FlapParser;

pub fn parse_program(input: &str) -> anyhow::Result<Block> {
    let mut pairs = FlapParser::parse(Rule::program, input).context("Autogen parser")?;
    let program_pair = pairs.next().unwrap();

    parse_statements(program_pair.into_inner())
}

fn parse_statements(pairs: Pairs<Rule>) -> anyhow::Result<Block> {
    let mut statements = Vec::new();
    for statement_pair in pairs {
        match statement_pair.as_rule() {
            Rule::statement => {
                statements.push(parse_statement(statement_pair)?);
            }
            Rule::EOI => {}
            _ => bail!("Got unexpected rule: {:?}", statement_pair.as_rule()),
        }
    }

    Ok(Block { statements })
}

fn parse_statement(pair: Pair<Rule>) -> anyhow::Result<Statement> {
    let target = pair.into_inner().next().unwrap();

    match target.as_rule() {
        Rule::function_call => Ok(Statement::FunctionCall(parse_function_call(target)?)),
        Rule::function_def => {
            let mut inner = target.into_inner();
            let return_type = parse_type(inner.next().unwrap())?;
            let function = parse_ident(inner.next().unwrap())?;

            let mut last_arg_type = None;
            let mut arguements = Vec::new();
            let mut statements = Vec::new();

            for pair in inner {
                match pair.as_rule() {
                    Rule::var_type => {
                        last_arg_type = Some(parse_type(pair)?);
                    }
                    Rule::ident => {
                        let Some(last_arg_type) = last_arg_type.take() else {
                            bail!("Got var name before var type: {:?}", pair.as_rule())
                        };

                        let ident = parse_ident(pair)?;
                        arguements.push((last_arg_type, ident));
                    }
                    Rule::statement => {
                        statements.push(parse_statement(pair)?);
                    }
                    _ => bail!(
                        "Unsupported function paramaters token: {:?}",
                        pair.as_rule()
                    ),
                }
            }

            Ok(Statement::FunctionDef(FunctionDef {
                function,
                arguements,
                contents: Block { statements },
                return_type,
            }))
        }
        Rule::static_var => {
            let mut inner = target.into_inner();
            let var_type = parse_type(inner.next().unwrap())?;
            let name = parse_ident(inner.next().unwrap())?;
            let value = parse_value(inner.next().unwrap())?;

            Ok(Statement::Static(StaticDef {
                name,
                var_type,
                value,
            }))
        }
        Rule::local_var => {
            let mut inner = target.into_inner();
            let var_type = parse_type(inner.next().unwrap())?;
            let name = parse_ident(inner.next().unwrap())?;
            let expr = parse_expr(inner.next().unwrap().into_inner())?;

            Ok(Statement::Local(LocalDef {
                name,
                var_type,
                expr,
            }))
        }
        Rule::return_statement => {
            let mut inner = target.into_inner();
            let value = parse_expr(inner.next().unwrap().into_inner())?;

            Ok(Statement::Return(value))
        }
        Rule::if_statement => {
            let mut inner = target.into_inner();
            let mut cases = Vec::new();
            let mut otherwise = None;

            for pair in inner {
                match pair.as_rule() {
                    Rule::if_block => {
                        cases.push(parse_if_block(pair)?);
                    }
                    Rule::else_block => {
                        otherwise = Some(parse_statements(pair.into_inner())?);
                    }
                    _ => bail!("Unsupported if_block type: {:?}", pair.as_rule()),
                }
            }

            Ok(Statement::If(IfStatement { cases, otherwise }))
        }
        _ => bail!("Unsupported statement type: {:?}", target.as_rule()),
    }
}

fn parse_if_block(pair: Pair<Rule>) -> anyhow::Result<IfCase> {
    let mut inner = pair.into_inner();
    let condition = parse_expr(inner.next().unwrap().into_inner())?;
    let contents = parse_statements(inner)?;

    Ok(IfCase {
        condition,
        contents,
    })
}

fn parse_type(pair: Pair<Rule>) -> anyhow::Result<Type> {
    let target = pair.into_inner().next().unwrap();

    match target.as_rule() {
        Rule::int_type => Ok(Type::Int),
        Rule::bool_type => Ok(Type::Bool),
        _ => bail!("Unexpected type: {:?}", target),
    }
}

fn parse_ident(pair: Pair<Rule>) -> anyhow::Result<Ident> {
    if !matches!(pair.as_rule(), Rule::ident) {
        bail!("Got {:?}, expected ident", pair);
    }

    Ok(pair.as_str().to_string())
}

fn parse_expr(pairs: Pairs<Rule>) -> anyhow::Result<Expr> {
    PRATT_PARSER
        .map_primary(|primary| {
            // Handle primary expressions (atoms)
            match primary.as_rule() {
                Rule::value => Ok(Expr::Value(parse_value(primary)?)),
                Rule::ident => Ok(Expr::Ident(parse_ident(primary)?)),
                Rule::expression => {
                    // Parenthesized expression
                    Ok(parse_expr(primary.into_inner())?)
                }
                Rule::function_call => Ok(Expr::FunctionCall(parse_function_call(primary)?)),
                _ => bail!("Unexpected primary: {:?}", primary),
            }
        })
        .map_infix(|lhs, op, rhs| {
            // Handle binary operations
            let bin_op = match op.as_rule() {
                Rule::add => BinaryOp::Add,
                Rule::subtract => BinaryOp::Sub,
                Rule::multiply => BinaryOp::Mul,
                Rule::divide => BinaryOp::Div,
                Rule::modulo => BinaryOp::Mod,
                Rule::power => BinaryOp::Pow,
                Rule::eq => BinaryOp::Eq,
                Rule::ne => BinaryOp::Ne,
                Rule::le => BinaryOp::Le,
                Rule::ge => BinaryOp::Ge,
                Rule::lt => BinaryOp::Lt,
                Rule::gt => BinaryOp::Gt,
                Rule::logical_and => BinaryOp::LAnd,
                Rule::logical_or => BinaryOp::LOr,
                _ => bail!("Unexpected infix op: {:?}", op),
            };
            Ok(Expr::BinaryOp {
                op: bin_op,
                left: Box::new(lhs?),
                right: Box::new(rhs?),
            })
        })
        .map_prefix(|op, rhs| {
            // Handle unary operations
            let un_op = match op.as_rule() {
                Rule::subtract => UnaryOp::Negate,
                Rule::logical_not => UnaryOp::LNot,
                _ => bail!("Unexpected prefix op: {:?}", op),
            };
            Ok(Expr::UnaryOp {
                op: un_op,
                operand: Box::new(rhs?),
            })
        })
        .parse(pairs)
}

fn parse_function_call(pair: Pair<Rule>) -> anyhow::Result<FunctionCall> {
    let mut inner = pair.into_inner();
    let function = parse_ident(inner.next().unwrap())?;

    Ok(FunctionCall {
        function,
        paramaters: inner
            .map(|it| it.into_inner())
            .map(parse_expr)
            .collect::<anyhow::Result<_>>()?,
    })
}

fn parse_value(pair: Pair<Rule>) -> anyhow::Result<Value> {
    let target = pair.into_inner().next().unwrap();

    match target.as_rule() {
        Rule::number => Ok(Value::Int(target.as_str().parse()?)),
        Rule::boolean => Ok(Value::Bool(target.as_str().parse()?)),
        _ => bail!("Unexpected value: {:?}", target),
    }
}
