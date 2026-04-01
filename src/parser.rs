use std::{
    collections::{BTreeMap, HashSet},
    path::Path,
};

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
use tracing::trace;

use crate::{
    ast::{
        Assignment, BinaryOp, Block, ConstDef, DeferedCaptures, DeferedType, Directive, Expr,
        FunctionAttribute, FunctionCall, FunctionDef, FunctionSignature, IdentRef, IfCase, IfExpr,
        LocalDef, PostfixOp, PrefixOp, Program, Punctuation, Statement, Type, Typedef, Value,
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
            .op(Op::infix(bit_and, Left))
            .op(Op::infix(eq, Left) | Op::infix(ne, Left))                    // == !=
            .op(Op::infix(le, Left) | Op::infix(ge, Left) | Op::infix(lt, Left) | Op::infix(gt, Left))  // <= >= < >
            .op(Op::infix(shl, Left) | Op::infix(shr, Left))
            .op(Op::infix(add, Left) | Op::infix(subtract, Left))             // + -
            .op(Op::infix(multiply, Left) | Op::infix(divide, Left) | Op::infix(modulo, Left))  // * / %
            .op(Op::prefix(cast))
            .op(Op::prefix(dereference) | Op::prefix(logical_not) | Op::prefix(negate))               // ! - (unary)
            // Highest precedence
            .op(Op::postfix(member) | Op::postfix(member_deref) | Op::postfix(array_idx))
    };
}

#[derive(Parser)]
#[grammar = "../grammars/flap.pest"]
struct FlapParser;

pub fn parse_program<'a>(input: &'a str) -> Result<Program<'a>> {
    let mut pairs = FlapParser::parse(Rule::program, input).wrap_err("Autogen parser")?;
    trace!("Input program tokens: {pairs:#?}");

    let mut directives = Vec::new();

    let pairs = pairs.next().unwrap().into_inner();
    for pair in pairs {
        match pair.as_rule() {
            Rule::directive => {
                directives.push(parse_directive(pair)?);
            }
            Rule::program_inner => {
                let code = parse_block_like(pair)?;

                return Ok(Program { directives, code });
            }
            _ => {
                return Err(
                    eyre!("Unsupported token at top level: {:?}", pair.as_rule())
                        .with_section(|| generate_span_error_section(pair.as_span())),
                );
            }
        }
    }

    unreachable!()
}

fn parse_directive(pair: Pair<Rule>) -> Result<Directive> {
    let kind = pair.into_inner().next().unwrap();

    match kind.as_rule() {
        Rule::include => Ok(Directive::Include(Path::new(
            kind.into_inner()
                .next()
                .unwrap()
                .into_inner()
                .next()
                .unwrap()
                .as_str(),
        ))),
        _ => {
            return Err(eyre!("Unsupported directive: {:?}", kind.as_rule())
                .with_section(|| generate_span_error_section(kind.as_span())));
        }
    }
}

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
                let var_type = parse_inferable_type(inner.next().unwrap())?;
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
                let var_type = parse_inferable_type(inner.next().unwrap())?;
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
            Rule::assignment => {
                let mut inner = target.into_inner();

                let target_pair = inner.next().unwrap();
                let target = parse_expr(target_pair.into_inner())?;

                let expr_pair = inner.next().unwrap();
                let expr_span = expr_pair.as_span();
                let expr = parse_expr(expr_pair.into_inner())?;

                Statement::Assignment(Assignment {
                    target,
                    expr,
                    span,
                    expr_span,
                    target_type: DeferedType::UnresolvedType,
                    expr_type: DeferedType::UnresolvedType,
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

fn parse_inferable_type(pair: Pair<Rule>) -> Result<DeferedType> {
    let mut tokens = pair.into_inner();
    let type_token = tokens.next().unwrap();

    match type_token.as_rule() {
        Rule::auto_type => Ok(DeferedType::UnresolvedType),
        Rule::var_type => Ok(DeferedType::ResolvedType(parse_type(type_token)?)),
        _ => {
            return Err(eyre!("Unknown inferable type: {:?}", type_token)
                .with_section(|| generate_span_error_section(type_token.as_span())));
        }
    }
}

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
        Rule::pointer_type_mod => Ok(Type::Pointer(acc?.into())),
        Rule::array_type_mod => Ok(Type::Array(
            acc?.into(),
            parse_number(next.into_inner().next().unwrap())?,
        )),
        _ => {
            return Err(
                eyre!("Unknown symbol trailing after type: {:?}", span.as_str())
                    .with_section(|| generate_span_error_section(span)),
            );
        }
    })
}

fn parse_ident(pair: Pair<Rule>) -> Result<IdentRef> {
    if !matches!(pair.as_rule(), Rule::ident) {
        return Err(eyre!("Got {:?}, expected ident", pair)
            .with_section(|| generate_span_error_section(pair.as_span())));
    }

    Ok(pair.as_str())
}

fn parse_expr(pairs: Pairs<Rule>) -> Result<Expr> {
    PRATT_PARSER
        .map_primary(|primary| {
            let span = primary.as_span();

            // Handle primary expressions (atoms)
            match primary.as_rule() {
                Rule::value => Ok(Expr::Value(parse_value(primary)?, span)),
                Rule::ident => Ok(Expr::Variable(parse_ident(primary)?, span)),
                Rule::expression => {
                    // Parenthesized expression
                    Ok(parse_expr(primary.into_inner())?)
                }
                Rule::function_call => Ok(Expr::FunctionCall(parse_function_call(primary)?)),
                Rule::sizeof_builtin => {
                    let inner = primary.clone().into_inner().next().unwrap();
                    match inner.as_rule() {
                        Rule::var_type => Ok(Expr::SizeOfType(parse_type(inner)?, span)),
                        Rule::expression => Ok(Expr::SizeOfExpr(
                            parse_expr(inner.into_inner())?.into(),
                            DeferedType::UnresolvedType,
                            span,
                        )),
                        _ => {
                            return Err(eyre!("Unsupported arguement to sizeof: {:?}", primary)
                                .with_section(|| generate_span_error_section(span)));
                        }
                    }
                }
                Rule::line_builtin => Ok(Expr::Value(
                    Value::Int(span.start_pos().line_col().0 as ClacValue),
                    span,
                )),
                Rule::if_statement => Ok(Expr::If(parse_if_expr(primary)?)),
                Rule::struct_expr => {
                    let struct_expr_fields = primary.into_inner();
                    let mut map = BTreeMap::new();

                    for struct_value_field in struct_expr_fields {
                        let mut field_tokens = struct_value_field.into_inner();

                        let field_name = parse_ident(field_tokens.next().unwrap())?;
                        let field_expr = parse_expr(field_tokens.next().unwrap().into_inner())?;
                        assert!(field_tokens.next().is_none());

                        map.insert(field_name, field_expr);
                    }

                    Ok(Expr::Struct(map, DeferedType::UnresolvedType, span))
                }
                Rule::array_expr => {
                    let array_value_fields = primary.into_inner();
                    let mut exprs = Vec::new();

                    for array_value_field in array_value_fields {
                        let expr = parse_expr(array_value_field.into_inner())?;

                        exprs.push(expr);
                    }

                    Ok(Expr::Array(exprs, DeferedType::UnresolvedType, span))
                }
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
            let pre_op = match op.as_rule() {
                Rule::cast => PrefixOp::Cast(parse_type(op.clone().into_inner().next().unwrap())?),
                Rule::dereference => PrefixOp::Dereference,
                Rule::negate => PrefixOp::Negate,
                Rule::logical_not => PrefixOp::LNot,
                _ => {
                    return Err(eyre!("Unexpected prefix op: {:?}", op)
                        .with_section(|| generate_span_error_section(op.as_span())));
                }
            };
            Ok(Expr::PrefixOp {
                op: pre_op,
                operand: Box::new(rhs?),
                span: op.as_span(),
                operand_type: DeferedType::UnresolvedType,
            })
        })
        .map_postfix(|lhs, op| {
            let post_op = match op.as_rule() {
                Rule::member => {
                    PostfixOp::Member(parse_ident(op.clone().into_inner().next().unwrap())?)
                }
                Rule::member_deref => {
                    PostfixOp::MemberDeref(parse_ident(op.clone().into_inner().next().unwrap())?)
                }
                Rule::array_idx => {
                    PostfixOp::ArrayIndex(parse_expr(op.clone().into_inner())?.into())
                }
                _ => {
                    return Err(eyre!("Unexpected postfix op: {:?}", op)
                        .with_section(|| generate_span_error_section(op.as_span())));
                }
            };

            Ok(Expr::PostfixOp {
                op: post_op,
                operand: Box::new(lhs?),
                span: op.as_span(),
                operand_type: DeferedType::UnresolvedType,
            })
        })
        .parse(pairs)
}

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

fn parse_number(pair: Pair<Rule>) -> Result<ClacValue> {
    parse_int::parse(pair.as_str()).with_section(|| generate_span_error_section(pair.as_span()))
}

fn parse_value(pair: Pair<Rule>) -> Result<Value> {
    let target = pair.into_inner().next().unwrap();

    match target.as_rule() {
        Rule::number => Ok(Value::Int(parse_number(target)?)),
        Rule::boolean => Ok(Value::Bool(target.as_str().parse()?)),
        Rule::char => Ok(Value::Char(
            target
                .as_str()
                .replace("\\n", "\n")
                .replace("\\t", "\t")
                .replace("\\0", "\0")
                .chars()
                .nth(1)
                .context("char")? as ClacValue,
        )),
        Rule::string => Ok(Value::String(
            target
                .into_inner()
                .next()
                .unwrap()
                .as_str()
                .replace("\\n", "\n")
                .replace("\\t", "\t")
                .replace("\\0", "\0")
                .into(),
        )),
        _ => {
            return Err(eyre!("Unexpected value: {:?}", target)
                .with_section(|| generate_span_error_section(target.as_span())));
        }
    }
}
