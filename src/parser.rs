use std::collections::HashSet;

use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Result, eyre},
};
use pest::{
    Parser,
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
};
use pest_derive::Parser;
use tracing::{instrument, trace};

use crate::{
    ast::{
        BinaryOp, Block, ConstDef, DeferedCaptures, DeferedType, Expr, FunctionAttribute,
        FunctionCall, FunctionDef, IdentRef, IfCase, IfExpr, LocalDef, Punctuation, Statement,
        Type, UnaryOp, Value,
    },
    middleware::generate_span_error_section,
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
            .op(Op::infix(shl, Left) | Op::infix(shr, Left))
            .op(Op::infix(bit_and, Left))
            // Highest precedence
            .op(Op::prefix(logical_not) | Op::prefix(negate))               // ! - (unary)
    };
}

#[derive(Parser)]
#[grammar = "../grammers/flap.pest"]
struct FlapParser;

#[instrument]
pub fn parse_program<'a>(input: &'a str) -> Result<Block<'a>> {
    let mut pairs = FlapParser::parse(Rule::program, input).wrap_err("Autogen parser")?;
    trace!("Input program tokens: {pairs:#?}");

    let program_contents_pair = pairs.next().unwrap();

    parse_block_like(program_contents_pair)
}

#[instrument]
fn parse_block_like(pair: Pair<Rule>) -> Result<Block> {
    trace!("Input block_like tokens: {pair:#?}");
    let span = pair.as_span();

    let mut statements = Vec::new();

    // Manual iteration so we can use peek
    let mut pairs = pair.into_inner();
    while let Some(target) = pairs.next() {
        trace!("Input statement tokens: {target:#?}");
        let span = target.as_span();

        let statement = match target.as_rule() {
            Rule::expression => {
                let punctuation = if pairs.peek().map(|it| it.as_rule()) == Some(Rule::semicolon) {
                    Punctuation::Punctuated
                } else {
                    Punctuation::Unpunctuated
                };

                Statement::Expr(parse_expr(target.into_inner())?, punctuation)
            }
            Rule::function_def => {
                let mut inner = target.into_inner();

                let mut attributes = HashSet::new();
                while let Some(Rule::function_attr) = inner.peek().map(|it| it.as_rule()) {
                    let attrubute = inner.next().unwrap();
                    for pair in attrubute.into_inner() {
                        match pair.as_rule() {
                            Rule::no_mangle => {
                                attributes.insert(FunctionAttribute::NoMangle);
                            }
                            _ => {
                                return Err(eyre!(
                                    "Unsupported function attr token: {:?}",
                                    pair.as_rule()
                                )
                                .with_section(|| generate_span_error_section(pair.as_span())));
                            }
                        }
                    }
                }

                let return_type = parse_type(inner.next().unwrap())?;
                let function = parse_ident(inner.next().unwrap())?;

                let mut last_arg_type = None;
                let mut arguements = Vec::new();
                let mut block = None;

                for pair in inner {
                    match pair.as_rule() {
                        Rule::var_type => {
                            last_arg_type = Some(parse_type(pair)?);
                        }
                        Rule::ident => {
                            let Some(last_arg_type) = last_arg_type.take() else {
                                return Err(eyre!(
                                    "Got var name before var type: {:?}",
                                    pair.as_rule()
                                )
                                .with_section(|| generate_span_error_section(pair.as_span())));
                            };

                            let ident = parse_ident(pair)?;
                            arguements.push((last_arg_type, ident));
                        }
                        Rule::block => {
                            block = Some(parse_block_like(pair)?);
                            break;
                        }
                        _ => {
                            return Err(eyre!(
                                "Unsupported function paramaters token: {:?}",
                                pair.as_rule()
                            )
                            .with_section(|| generate_span_error_section(pair.as_span())));
                        }
                    }
                }

                Statement::FunctionDef(FunctionDef {
                    attributes,
                    function,
                    arguements,
                    contents: block
                        .wrap_err("Function def did not contain block")
                        .with_section(|| generate_span_error_section(span))?,
                    return_type,
                    span,
                    captures: DeferedCaptures::UnresolvedCaptures,
                })
            }
            Rule::const_var => {
                let mut inner = target.into_inner();
                let var_type = parse_type(inner.next().unwrap())?;
                let name = parse_ident(inner.next().unwrap())?;

                let value_pair = inner.next().unwrap();
                let value_span = value_pair.as_span();
                let value = parse_value(value_pair)?;

                Statement::Const(ConstDef {
                    name,
                    var_type,
                    value,
                    span,
                    value_span,
                })
            }
            Rule::local_var => {
                let mut inner = target.into_inner();
                let var_type = parse_type(inner.next().unwrap())?;
                let name = parse_ident(inner.next().unwrap())?;
                let expr = parse_expr(inner.next().unwrap().into_inner())?;

                Statement::Local(LocalDef {
                    name,
                    var_type,
                    expr,
                    span,
                })
            }
            Rule::semicolon => continue,
            Rule::EOI => continue,
            _ => {
                return Err(eyre!("Unsupported statement type: {:?}", target.as_rule())
                    .with_section(|| generate_span_error_section(target.as_span())));
            }
        };

        statements.push(statement);
    }

    Ok(Block {
        statements,
        span,
        captures: DeferedCaptures::UnresolvedCaptures,
    })
}

#[instrument]
fn parse_if_expr(pair: Pair<Rule>) -> Result<IfExpr> {
    let span = pair.as_span();
    let inner = pair.into_inner();
    let mut cases = Vec::new();
    let mut otherwise = None;

    for pair in inner {
        match pair.as_rule() {
            Rule::if_block => {
                cases.push(parse_if_block(pair)?);
            }
            Rule::else_block => {
                otherwise = Some(parse_block_like(pair.into_inner().next().unwrap())?);
            }
            _ => {
                return Err(eyre!("Unsupported if_block type: {:?}", pair.as_rule())
                    .with_section(|| generate_span_error_section(pair.as_span())));
            }
        }
    }

    Ok(IfExpr {
        cases,
        otherwise,
        span,
        return_type: DeferedType::UnresolvedType,
        captures: DeferedCaptures::UnresolvedCaptures,
    })
}

#[instrument]
fn parse_if_block(pair: Pair<Rule>) -> Result<IfCase> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let condition = parse_expr(inner.next().unwrap().into_inner())?;
    let contents = parse_block_like(inner.next().unwrap())?;

    Ok(IfCase {
        condition,
        contents,
        span,
    })
}

#[instrument]
fn parse_type(pair: Pair<Rule>) -> Result<Type> {
    let target = pair.into_inner().next().unwrap();

    match target.as_rule() {
        Rule::int_type => Ok(Type::Int),
        Rule::bool_type => Ok(Type::Bool),
        Rule::void_type => Ok(Type::Void),
        _ => {
            return Err(eyre!("Unknown type: {:?}", target)
                .with_section(|| generate_span_error_section(target.as_span())));
        }
    }
}

#[instrument]
fn parse_ident(pair: Pair<Rule>) -> Result<IdentRef> {
    if !matches!(pair.as_rule(), Rule::ident) {
        return Err(eyre!("Got {:?}, expected ident", pair)
            .with_section(|| generate_span_error_section(pair.as_span())));
    }

    Ok(pair.as_str())
}

#[instrument]
fn parse_expr(pairs: Pairs<Rule>) -> Result<Expr> {
    PRATT_PARSER
        .map_primary(|primary| {
            let span = primary.as_span();

            // Handle primary expressions (atoms)
            match primary.as_rule() {
                Rule::value => Ok(Expr::Value(parse_value(primary)?, span)),
                Rule::ident => Ok(Expr::Ident(parse_ident(primary)?, span)),
                Rule::expression => {
                    // Parenthesized expression
                    Ok(parse_expr(primary.into_inner())?)
                }
                Rule::function_call => Ok(Expr::FunctionCall(parse_function_call(primary)?)),
                Rule::if_statement => Ok(Expr::If(parse_if_expr(primary)?)),
                _ => {
                    return Err(eyre!("Unexpected primary: {:?}", primary)
                        .with_section(|| generate_span_error_section(span)));
                }
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
                Rule::shr => BinaryOp::BShr,
                Rule::shl => BinaryOp::BShl,
                Rule::bit_and => BinaryOp::BAnd,
                _ => {
                    return Err(eyre!("Unexpected infix op: {:?}", op)
                        .with_section(|| generate_span_error_section(op.as_span())));
                }
            };
            Ok(Expr::BinaryOp {
                op: bin_op,
                left: Box::new(lhs?),
                right: Box::new(rhs?),
                span: op.as_span(),
            })
        })
        .map_prefix(|op, rhs| {
            // Handle unary operations
            let un_op = match op.as_rule() {
                Rule::negate => UnaryOp::Negate,
                Rule::logical_not => UnaryOp::LNot,
                _ => {
                    return Err(eyre!("Unexpected prefix op: {:?}", op)
                        .with_section(|| generate_span_error_section(op.as_span())));
                }
            };
            Ok(Expr::UnaryOp {
                op: un_op,
                operand: Box::new(rhs?),
                span: op.as_span(),
            })
        })
        .parse(pairs)
}

#[instrument]
fn parse_function_call(pair: Pair<Rule>) -> Result<FunctionCall> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let function = parse_ident(inner.next().unwrap())?;

    Ok(FunctionCall {
        function,
        parameters: inner
            .map(|it| it.into_inner())
            .map(parse_expr)
            .collect::<Result<_>>()?,
        span,
    })
}

#[instrument]
fn parse_value(pair: Pair<Rule>) -> Result<Value> {
    let target = pair.into_inner().next().unwrap();

    match target.as_rule() {
        Rule::number => Ok(Value::Int(
            parse_int::parse(target.as_str())
                .with_section(|| generate_span_error_section(target.as_span()))?,
        )),
        Rule::boolean => Ok(Value::Bool(target.as_str().parse()?)),
        _ => {
            return Err(eyre!("Unexpected value: {:?}", target)
                .with_section(|| generate_span_error_section(target.as_span())));
        }
    }
}
