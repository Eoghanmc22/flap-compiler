use std::collections::{BTreeMap, HashSet};

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
        FunctionCall, FunctionDef, FunctionSignature, IdentRef, IfCase, IfExpr, LocalDef,
        PtrAssign, Punctuation, Statement, Type, Typedef, UnaryOp, Value,
    },
    codegen::clac::ClacValue,
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
            .op(Op::prefix(cast))
            // Highest precedence
            .op(Op::prefix(pointer_type) | Op::prefix(logical_not) | Op::prefix(negate))               // ! - (unary)
    };
}

#[derive(Parser)]
#[grammar = "../grammars/flap.pest"]
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
            Rule::if_statement => {
                let punctuation =
                    if matches!(pairs.peek().map(|it| it.as_rule()), Some(Rule::EOI) | None) {
                        Punctuation::Unpunctuated
                    } else {
                        Punctuation::Punctuated
                    };

                Statement::Expr(Expr::If(parse_if_expr(target)?), punctuation)
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
                    contents: block
                        .wrap_err("Function def did not contain block")
                        .with_section(|| generate_span_error_section(span))?,
                    signature: FunctionSignature {
                        arguements,
                        return_type,
                    },
                    span,
                    captures: DeferedCaptures::UnresolvedCaptures,
                })
            }
            Rule::const_var => {
                let mut inner = target.into_inner();
                let var_type = parse_type(inner.next().unwrap())?;
                let name = parse_ident(inner.next().unwrap())?;

                let expr_pair = inner.next().unwrap();
                let expr_span = expr_pair.as_span();
                let expr = parse_expr(expr_pair.into_inner())?;

                Statement::Const(ConstDef {
                    name,
                    var_type,
                    expr,
                    span,
                    expr_span,
                })
            }
            Rule::local_var => {
                let mut inner = target.into_inner();
                let var_type = parse_type(inner.next().unwrap())?;
                let name = parse_ident(inner.next().unwrap())?;

                let expr_pair = inner.next().unwrap();
                let expr_span = expr_pair.as_span();
                let expr = parse_expr(expr_pair.into_inner())?;

                Statement::Local(LocalDef {
                    name,
                    var_type,
                    expr,
                    span,
                    expr_span,
                })
            }
            Rule::pointer_assign => {
                let mut inner = target.into_inner();

                let target_pair = inner.next().unwrap();
                let target = parse_expr(target_pair.into_inner())?;

                let expr_pair = inner.next().unwrap();
                let expr_span = expr_pair.as_span();
                let expr = parse_expr(expr_pair.into_inner())?;

                Statement::PtrAssign(PtrAssign {
                    target,
                    expr,
                    span,
                    expr_span,
                    value_type: DeferedType::UnresolvedType,
                })
            }
            Rule::typedef => {
                let mut inner = target.into_inner();
                let type_alias = parse_type(inner.next().unwrap())?;
                let name = parse_ident(inner.next().unwrap())?;

                Statement::Typedef(Typedef {
                    name,
                    type_alias,
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
    let span = pair.as_span();
    let mut tokens = pair.into_inner();
    let type_token = tokens.next().unwrap();

    let parsed_type = match type_token.as_rule() {
        Rule::char_type => Type::Char,
        Rule::int_type => Type::Int,
        Rule::bool_type => Type::Bool,
        Rule::void_type => Type::Void,
        Rule::struct_type => {
            let struct_type_fields = type_token.into_inner();
            let mut map = BTreeMap::new();

            for struct_type_field in struct_type_fields {
                let mut field_tokens = struct_type_field.into_inner();

                let field_type = parse_type(field_tokens.next().unwrap())?;
                let field_name = parse_ident(field_tokens.next().unwrap())?;
                assert!(field_tokens.next().is_none());

                map.insert(field_name, field_type);
            }

            Type::Struct(map)
        }
        Rule::named_type => Type::Typedef(type_token.as_str()),
        _ => {
            return Err(eyre!("Unknown type: {:?}", type_token)
                .with_section(|| generate_span_error_section(type_token.as_span())));
        }
    };

    tokens.fold(Ok(parsed_type), |acc, next| match next.as_rule() {
        Rule::pointer_type => Ok(Type::Pointer(acc?.into())),
        _ => {
            return Err(
                eyre!("Unknown symbol trailing after type: {:?}", span.as_str())
                    .with_section(|| generate_span_error_section(span)),
            );
        }
    })
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
                Rule::field_path => Ok(Expr::Path(
                    primary
                        .into_inner()
                        .map(parse_ident)
                        .collect::<Result<_>>()?,
                    span,
                )),
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
                left_type: DeferedType::UnresolvedType,
                right_type: DeferedType::UnresolvedType,
            })
        })
        .map_prefix(|op, rhs| {
            // Handle unary operations
            let un_op = match op.as_rule() {
                Rule::cast => UnaryOp::Cast(parse_type(op.clone().into_inner().next().unwrap())?),
                Rule::dereference => UnaryOp::Dereference,
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
                operand_type: DeferedType::UnresolvedType,
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
        Rule::char => Ok(Value::Char(
            target
                .as_str()
                .replace("\\n", "\n")
                .replace("\\t", "\t")
                .chars()
                .nth(1)
                .context("char")? as ClacValue,
        )),
        Rule::struct_value => {
            let struct_value_fields = target.into_inner();
            let mut map = BTreeMap::new();

            for struct_value_field in struct_value_fields {
                let mut field_tokens = struct_value_field.into_inner();

                let field_name = parse_ident(field_tokens.next().unwrap())?;
                let field_value = parse_value(field_tokens.next().unwrap())?;
                assert!(field_tokens.next().is_none());

                map.insert(field_name, field_value);
            }

            Ok(Value::Struct(map))
        }
        _ => {
            return Err(eyre!("Unexpected value: {:?}", target)
                .with_section(|| generate_span_error_section(target.as_span())));
        }
    }
}
