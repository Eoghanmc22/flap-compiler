use core::cmp;
use std::{borrow::Cow, collections::HashSet, path::Path, ptr};

use pest::{
    Parser, Span,
    error::ErrorVariant,
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
};
use pest_derive::Parser;
use tracing::trace;

use crate::{
    ast::{
        AnnotatedSpan, Arguement, Assignment, AstSpan, BinaryOp, Block, ConstDef, DeferedAddress,
        DeferedCaptures, DeferedType, DeferedVersion, Directive, Expr, FunctionAttribute,
        FunctionCall, FunctionDef, FunctionSignature, IdentRef, IfCase, IfExpr, LocalDef, Loop,
        PostfixOp, PrefixOp, Program, Punctuation, SizeOfMode, Statement, Type, Typedef, Value,
    },
    codegen::clac::{ClacValue, ClacValueUnsigned},
    error::ParserError,
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
            .op(Op::prefix(dereference) | Op::prefix(logical_not) | Op::prefix(negate) | Op::prefix(invert) | Op::prefix(addrs_of))               // ! - (unary)
            // Highest precedence
            .op(Op::postfix(member) | Op::postfix(member_deref) | Op::postfix(array_idx))
    };
}

pub fn merge_spans<'i>(a: &AnnotatedSpan<'i>, b: &AnnotatedSpan<'i>) -> Option<AnnotatedSpan<'i>> {
    if a.file_name != b.file_name || !ptr::eq(a.span.get_input(), b.span.get_input()) {
        return None;
    }

    Some(AnnotatedSpan {
        span: merge_pest_spans(a.span, b.span)?,
        file_name: a.file_name,
    })
}

pub fn merge_pest_spans<'i>(a: Span<'i>, b: Span<'i>) -> Option<Span<'i>> {
    Span::new(
        a.get_input(),
        cmp::min(a.start(), b.start()),
        cmp::max(a.end(), b.end()),
    )
}

#[derive(Parser)]
#[grammar = "../grammars/flap.pest"]
struct FlapParser;

pub type PestError = pest::error::Error<Rule>;
type Result<T, E = PestError> = core::result::Result<T, E>;

fn rule_renamer(rule: &Rule) -> String {
    match rule {
        Rule::EOI => "End of File",
        Rule::multiline_comment => "comment",
        Rule::singleline_comment => "comment",
        Rule::COMMENT => "comment",
        Rule::WHITESPACE => "whitespace",
        Rule::escape => "escape code",
        Rule::char_inner => "char",
        Rule::char => "char",
        Rule::string_inner => "string",
        Rule::string => "string",
        Rule::number => "number",
        Rule::r#true => "true",
        Rule::r#false => "false",
        Rule::boolean => "bool",
        Rule::value => "value",
        Rule::ident_start_chars => "ident",
        Rule::ident_chars => "ident",
        Rule::ident => "ident",
        Rule::struct_type_field => "field type",
        Rule::struct_type => "struct type",
        Rule::struct_expr_field => "field expr",
        Rule::struct_expr => "struct initializer",
        Rule::array_expr => "array initializer",
        Rule::array_type_mod => "array type",
        Rule::pointer_type_mod => "pointer type",
        Rule::type_mod => "type modifier",
        Rule::char_type => "char type",
        Rule::int_type => "int type",
        Rule::bool_type => "bool type",
        Rule::void_type => "void type",
        Rule::named_type => "named type",
        Rule::var_type => "type",
        Rule::primitive_type => "type",
        Rule::typedef => "typedef",
        Rule::add => "+",
        Rule::subtract => "-",
        Rule::negate => "-",
        Rule::invert => "~",
        Rule::multiply => "*",
        Rule::divide => "/",
        Rule::modulo => "%",
        Rule::eq => "==",
        Rule::ne => "!=",
        Rule::le => "<=",
        Rule::ge => ">=",
        Rule::lt => "<",
        Rule::gt => ">",
        Rule::logical_and => "&&",
        Rule::logical_or => "||",
        Rule::logical_not => "!",
        Rule::shr => ">>",
        Rule::shl => "<<",
        Rule::bit_and => "&",
        Rule::dereference => "*",
        Rule::cast => "(type)",
        Rule::member => ".ident",
        Rule::member_deref => "->ident",
        Rule::array_idx => "[expr]",
        Rule::addrs_of => "&",
        Rule::binary_op => "binary op",
        Rule::prefix_op => "prefix op",
        Rule::postfix_op => "postfix_op",
        Rule::atom => "expr atom",
        Rule::expression => "expr",
        Rule::auto_type => "auto",
        Rule::inferable_type => "type",
        Rule::const_var => "constant def",
        Rule::local_var => "local def",
        Rule::assignment => "assignment",
        Rule::function_parameters => "function parameters",
        Rule::function_call => "function call",
        Rule::sizeof_builtin => "sizeof",
        Rule::global_builtin => "global",
        Rule::box_builtin => "box",
        Rule::sizeof_packed_builtin => "sizeof_packed",
        Rule::line_builtin => "__LINE__",
        Rule::if_block => "if",
        Rule::if_else_block => "else if",
        Rule::else_block => "else",
        Rule::if_statement => "if statement",
        Rule::while_loop => "while loop",
        Rule::for_loop => "for loop",
        Rule::forever => "loop",
        Rule::defer_block => "defer",
        Rule::include => "#include",
        Rule::directive => "directive",
        Rule::semicolon => ";",
        Rule::statement => "statememnt",
        Rule::no_mangle => "no_mangle",
        Rule::lang_item => "lang",
        Rule::no_captures => "no_captures",
        Rule::function_attr => "function attribute",
        Rule::function_attrs => "function attributes",
        Rule::function_parameters_def => "function parameters",
        Rule::function_def => "function definition",
        Rule::block => "block",
        Rule::code => "code",
        Rule::program_inner => "program",
        Rule::program => "program",
        Rule::program_directives => "directives",
        Rule::struct_kind_inorder => "inorder",
        Rule::struct_kind => "struct kind",
    }
    .to_string()
}

pub fn map_parser_error(err: PestError, file_name: &str, file_contents: &str) -> ParserError {
    let err = err.renamed_rules(rule_renamer);

    let renamer: pest::error::RuleToMessageFn<Rule> =
        Box::new(|rule: &Rule| Some(rule_renamer(rule)));
    let is_whitespace: pest::error::IsWhitespaceFn =
        Box::new(|str: String| FlapParser::parse(Rule::WHITESPACE, &str).is_ok());

    let extra = err.parse_attempts_error(file_contents, &renamer, &is_whitespace);

    let err = if let Some(extra) = extra { extra } else { err };

    let err = err.with_path(file_name);

    ParserError::PestError {
        inner: err,
        file_name: file_name.into(),
        file: file_contents.into(),
    }
}

pub fn parse_program<'a>(input: &'a str, file_name: &'a str) -> Result<Program<'a>> {
    let mut pairs = FlapParser::parse(Rule::program, input)?;
    trace!("Input program tokens: {pairs:#?}");

    let mut directives = Vec::new();

    let target = pairs.next().unwrap();
    let span = target.as_span();
    let pairs = target.into_inner();
    for pair in pairs {
        match pair.as_rule() {
            Rule::directive => {
                directives.push(parse_directive(pair, file_name)?);
            }
            Rule::program_inner => {
                let code = parse_block_like(pair, file_name)?;

                return Ok(Program {
                    directives,
                    code,
                    span: AnnotatedSpan { span, file_name },
                });
            }
            rule => {
                return Err(PestError::new_from_span(
                    ErrorVariant::ParsingError {
                        positives: vec![Rule::directive, Rule::program_inner],
                        negatives: vec![rule],
                    },
                    pair.as_span(),
                ));
            }
        }
    }

    unreachable!()
}

pub fn parse_directives<'a>(input: &'a str, file_name: &'a str) -> Result<Vec<Directive<'a>>> {
    let mut pairs = FlapParser::parse(Rule::program_directives, input)?;
    trace!("Input program tokens: {pairs:#?}");

    let mut directives = Vec::new();

    let pairs = pairs.next().unwrap().into_inner();
    for pair in pairs {
        match pair.as_rule() {
            Rule::directive => {
                directives.push(parse_directive(pair, file_name)?);
            }
            Rule::EOI => continue,
            rule => {
                return Err(PestError::new_from_span(
                    ErrorVariant::ParsingError {
                        positives: vec![Rule::directive, Rule::EOI],
                        negatives: vec![rule],
                    },
                    pair.as_span(),
                ));
            }
        }
    }

    return Ok(directives);
}

fn parse_directive<'a>(pair: Pair<'a, Rule>, file_name: &'a str) -> Result<Directive<'a>> {
    let kind = pair.into_inner().next().unwrap();
    let span = kind.as_span();

    match kind.as_rule() {
        Rule::include => Ok(Directive::Include(
            Path::new(
                kind.into_inner()
                    .next()
                    .unwrap()
                    .into_inner()
                    .next()
                    .unwrap()
                    .as_str(),
            ),
            AnnotatedSpan { span, file_name },
        )),
        rule => {
            return Err(PestError::new_from_span(
                ErrorVariant::ParsingError {
                    positives: vec![Rule::include],
                    negatives: vec![rule],
                },
                kind.as_span(),
            ));
        }
    }
}

fn parse_block_like<'a>(pair: Pair<'a, Rule>, file_name: &'a str) -> Result<Block<'a>> {
    trace!("Input block_like tokens: {pair:#?}");
    let span = pair.as_span();

    let mut statements = Vec::new();

    // Manual iteration so we can use peek
    let mut pairs = pair.into_inner();
    while let Some(target) = pairs.next() {
        trace!("Input statement tokens: {target:#?}");

        let statement = match target.as_rule() {
            Rule::expression => {
                let punctuation = if pairs.peek().map(|it| it.as_rule()) == Some(Rule::semicolon) {
                    Punctuation::Punctuated
                } else {
                    Punctuation::Unpunctuated
                };

                Statement::Expr(parse_expr(target.into_inner(), file_name)?, punctuation)
            }
            Rule::if_statement => Statement::Expr(
                Expr::If(parse_if_expr(target, file_name)?),
                Punctuation::Unpunctuated,
            ),
            Rule::function_def => Statement::FunctionDef(parse_function_def(target, file_name)?),
            Rule::const_var => Statement::Const(parse_const_var(target, file_name)?),
            Rule::local_var => Statement::Local(parse_local_var(target, file_name)?),
            Rule::assignment => Statement::Assignment(parse_assignment(target, file_name)?),
            Rule::typedef => Statement::Typedef(parse_typedef(target, file_name)?),
            Rule::defer_block => Statement::Defer(parse_block_like(
                target.into_inner().next().unwrap(),
                file_name,
            )?),
            Rule::for_loop | Rule::while_loop | Rule::forever => {
                Statement::Loop(parse_loop(target, file_name)?)
            }
            Rule::semicolon => continue,
            Rule::EOI => continue,
            rule => {
                return Err(PestError::new_from_span(
                    ErrorVariant::ParsingError {
                        positives: vec![
                            Rule::expression,
                            Rule::if_statement,
                            Rule::function_def,
                            Rule::const_var,
                            Rule::local_var,
                            Rule::assignment,
                            Rule::typedef,
                            Rule::defer_block,
                            Rule::for_loop,
                            Rule::while_loop,
                            Rule::forever,
                            Rule::semicolon,
                            Rule::EOI,
                        ],
                        negatives: vec![rule],
                    },
                    target.as_span(),
                ));
            }
        };

        statements.push(statement);
    }

    Ok(Block {
        statements,
        span: AnnotatedSpan { span, file_name },
        captures: DeferedCaptures::UnresolvedCaptures,
    })
}

fn parse_function_def<'a>(target: Pair<'a, Rule>, file_name: &'a str) -> Result<FunctionDef<'a>> {
    let span = target.as_span();
    let mut inner = target.into_inner();

    let mut attributes = HashSet::new();
    while let Some(Rule::function_attr) = inner.peek().map(|it| it.as_rule()) {
        let attrubute = inner.next().unwrap();
        for pair in attrubute.into_inner() {
            match pair.as_rule() {
                Rule::no_mangle => {
                    attributes.insert(FunctionAttribute::NoMangle);
                }
                Rule::no_captures => {
                    attributes.insert(FunctionAttribute::NoCaptures);
                }
                Rule::lang_item => {
                    attributes.insert(FunctionAttribute::LangItem(
                        parse_string(pair.into_inner().next().unwrap())?.to_string(),
                    ));
                }
                rule => {
                    return Err(PestError::new_from_span(
                        ErrorVariant::ParsingError {
                            positives: vec![Rule::no_mangle, Rule::lang_item, Rule::no_captures],
                            negatives: vec![rule],
                        },
                        pair.as_span(),
                    ));
                }
            }
        }
    }

    let return_token = inner.next().unwrap();
    let return_span = return_token.as_span();
    let return_type = parse_type(return_token, file_name)?;

    let function_token = inner.next().unwrap();
    let function_span = function_token.as_span();
    let function = parse_ident(function_token, file_name)?;

    let mut last_arg_type = None;
    let mut arguements = Vec::new();
    let mut arguements_span = merge_pest_spans(return_span, function_span).unwrap();

    for pair in inner {
        let pair_span = pair.as_span();

        let next_arguements_span = merge_pest_spans(arguements_span, pair_span).unwrap();

        match pair.as_rule() {
            Rule::var_type => {
                last_arg_type = Some((parse_type(pair, file_name)?, pair_span));
            }
            Rule::ident => {
                let Some((last_arg_type, type_span)) = last_arg_type.take() else {
                    return Err(PestError::new_from_span(
                        ErrorVariant::CustomError {
                            message: format!("Got var name before var type: {:?}", pair.as_rule()),
                        },
                        pair.as_span(),
                    ));
                };

                let span = AnnotatedSpan {
                    span: merge_pest_spans(type_span, pair.as_span()).unwrap(),
                    file_name,
                };
                let ident = parse_ident(pair, file_name)?;
                arguements.push(Arguement {
                    arg_type: last_arg_type,
                    arg_name: ident,
                    version: DeferedVersion::UnresolvedVersion,
                    span,
                });
            }
            Rule::block => {
                return Ok(FunctionDef {
                    attributes,
                    function,
                    contents: parse_block_like(pair, file_name)?,
                    signature: FunctionSignature {
                        arguements,
                        return_type,
                        captures: DeferedCaptures::UnresolvedCaptures,
                        span: AnnotatedSpan {
                            span: arguements_span,
                            file_name,
                        },
                    },
                    span: AnnotatedSpan { span, file_name },
                });
            }
            _ => {
                return Err(PestError::new_from_span(
                    ErrorVariant::CustomError {
                        message: format!(
                            "Unsupported function paramaters token: {:?}",
                            pair.as_rule()
                        ),
                    },
                    pair.as_span(),
                ));
            }
        }

        arguements_span = next_arguements_span;
    }

    Err(PestError::new_from_span(
        ErrorVariant::ParsingError {
            positives: vec![Rule::block],
            negatives: vec![],
        },
        span,
    ))
}

fn parse_const_var<'a>(target: Pair<'a, Rule>, file_name: &'a str) -> Result<ConstDef<'a>> {
    let span = target.as_span();
    let mut inner = target.into_inner();
    let var_type = parse_inferable_type(inner.next().unwrap(), file_name)?;
    let name = parse_ident(inner.next().unwrap(), file_name)?;

    let expr_pair = inner.next().unwrap();
    let expr = parse_expr(expr_pair.into_inner(), file_name)?;

    Ok(ConstDef {
        name,
        var_type,
        expr,
        span: AnnotatedSpan { span, file_name },
        version: DeferedVersion::UnresolvedVersion,
    })
}

fn parse_local_var<'a>(target: Pair<'a, Rule>, file_name: &'a str) -> Result<LocalDef<'a>> {
    let span = target.as_span();
    let mut inner = target.into_inner();
    let var_type = parse_inferable_type(inner.next().unwrap(), file_name)?;
    let name = parse_ident(inner.next().unwrap(), file_name)?;

    let expr_pair = inner.next().unwrap();
    let expr = parse_expr(expr_pair.into_inner(), file_name)?;

    Ok(LocalDef {
        name,
        var_type,
        expr,
        span: AnnotatedSpan { span, file_name },
        version: DeferedVersion::UnresolvedVersion,
    })
}

fn parse_assignment<'a>(target: Pair<'a, Rule>, file_name: &'a str) -> Result<Assignment<'a>> {
    let span = target.as_span();
    let mut inner = target.into_inner();

    let target_pair = inner.next().unwrap();
    let target = parse_expr(target_pair.into_inner(), file_name)?;

    let expr_pair = inner.next().unwrap();
    let expr_span = expr_pair.as_span();
    let expr = parse_expr(expr_pair.into_inner(), file_name)?;

    Ok(Assignment {
        target,
        expr,
        span: AnnotatedSpan { span, file_name },
        expr_span: AnnotatedSpan {
            span: expr_span,
            file_name,
        },
        target_type: DeferedType::UnresolvedType,
        expr_type: DeferedType::UnresolvedType,
    })
}

fn parse_typedef<'a>(target: Pair<'a, Rule>, file_name: &'a str) -> Result<Typedef<'a>> {
    let span = target.as_span();
    let mut inner = target.into_inner();
    let type_alias = parse_type(inner.next().unwrap(), file_name)?;
    let name = parse_ident(inner.next().unwrap(), file_name)?;

    Ok(Typedef {
        name,
        type_alias,
        span: AnnotatedSpan { span, file_name },
    })
}

fn parse_loop<'a>(target: Pair<'a, Rule>, file_name: &'a str) -> Result<Loop<'a>> {
    let span = target.as_span();

    let mut init = None;
    let mut cond = None;
    let mut update = None;

    for token in target.into_inner() {
        match token.as_rule() {
            Rule::local_var => {
                init = Some(parse_local_var(token, file_name)?);
            }
            Rule::expression => {
                cond = Some(parse_expr(token.into_inner(), file_name)?);
            }
            Rule::assignment => {
                update = Some(parse_assignment(token, file_name)?);
            }
            Rule::block => {
                return Ok(Loop {
                    init,
                    cond,
                    update,
                    body: parse_block_like(token, file_name)?,
                    span: AnnotatedSpan { span, file_name },
                    captures: DeferedCaptures::UnresolvedCaptures,
                });
            }
            rule => {
                return Err(PestError::new_from_span(
                    ErrorVariant::ParsingError {
                        positives: vec![
                            Rule::local_var,
                            Rule::assignment,
                            Rule::expression,
                            Rule::block,
                        ],
                        negatives: vec![rule],
                    },
                    token.as_span(),
                ));
            }
        }
    }

    Err(PestError::new_from_span(
        ErrorVariant::ParsingError {
            positives: vec![Rule::block],
            negatives: vec![],
        },
        span,
    ))
}

fn parse_if_expr<'a>(pair: Pair<'a, Rule>, file_name: &'a str) -> Result<IfExpr<'a>> {
    let span = pair.as_span();
    let inner = pair.into_inner();
    let mut cases = Vec::new();
    let mut otherwise = None;

    for pair in inner {
        match pair.as_rule() {
            Rule::if_block => {
                cases.push(parse_if_block(pair, file_name)?);
            }
            Rule::else_block => {
                otherwise = Some(parse_block_like(
                    pair.into_inner().next().unwrap(),
                    file_name,
                )?);
            }
            rule => {
                return Err(PestError::new_from_span(
                    ErrorVariant::ParsingError {
                        positives: vec![Rule::if_block, Rule::else_block],
                        negatives: vec![rule],
                    },
                    pair.as_span(),
                ));
            }
        }
    }

    Ok(IfExpr {
        cases,
        otherwise,
        span: AnnotatedSpan { span, file_name },
        return_type: DeferedType::UnresolvedType,
        captures: DeferedCaptures::UnresolvedCaptures,
    })
}

fn parse_if_block<'a>(pair: Pair<'a, Rule>, file_name: &'a str) -> Result<IfCase<'a>> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let condition = parse_expr(inner.next().unwrap().into_inner(), file_name)?;
    let contents = parse_block_like(inner.next().unwrap(), file_name)?;

    Ok(IfCase {
        condition,
        contents,
        span: AnnotatedSpan { span, file_name },
    })
}

fn parse_inferable_type<'a>(pair: Pair<'a, Rule>, file_name: &'a str) -> Result<DeferedType<'a>> {
    let mut tokens = pair.into_inner();
    let type_token = tokens.next().unwrap();

    match type_token.as_rule() {
        Rule::auto_type => Ok(DeferedType::UnresolvedType),
        Rule::var_type => Ok(DeferedType::ResolvedType(parse_type(
            type_token, file_name,
        )?)),
        rule => {
            return Err(PestError::new_from_span(
                ErrorVariant::ParsingError {
                    positives: vec![Rule::auto_type, Rule::var_type],
                    negatives: vec![rule],
                },
                type_token.as_span(),
            ));
        }
    }
}

fn parse_type<'a>(pair: Pair<'a, Rule>, file_name: &'a str) -> Result<Type<'a>> {
    let mut tokens = pair.into_inner();
    let type_token = tokens.next().unwrap();
    let span = type_token.as_span();

    let parsed_type = match type_token.as_rule() {
        Rule::primitive_type => {
            let type_token = type_token.into_inner().next().unwrap();

            match type_token.as_rule() {
                Rule::char_type => Type::Char,
                Rule::int_type => Type::Int,
                Rule::bool_type => Type::Bool,
                Rule::void_type => Type::Void,
                rule => {
                    return Err(PestError::new_from_span(
                        ErrorVariant::ParsingError {
                            positives: vec![
                                Rule::char_type,
                                Rule::int_type,
                                Rule::bool_type,
                                Rule::void_type,
                            ],
                            negatives: vec![rule],
                        },
                        type_token.as_span(),
                    ));
                }
            }
        }
        Rule::struct_type => {
            let mut struct_type_fields = type_token.into_inner();
            let mut fields = Vec::new();

            let constructor: &dyn Fn(_) -> _ = if struct_type_fields
                .peek()
                .map(|it| it.as_rule() == Rule::struct_kind)
                .unwrap_or(false)
            {
                let kind = struct_type_fields
                    .next()
                    .unwrap()
                    .into_inner()
                    .next()
                    .unwrap();

                match kind.as_rule() {
                    Rule::struct_kind_inorder => &|fields| Type::NamedTuple(fields),
                    rule => {
                        return Err(PestError::new_from_span(
                            ErrorVariant::ParsingError {
                                positives: vec![Rule::struct_kind_inorder],
                                negatives: vec![rule],
                            },
                            kind.as_span(),
                        ));
                    }
                }
            } else {
                &|fields| Type::Struct(fields.into_iter().collect())
            };

            for struct_type_field in struct_type_fields {
                let mut field_tokens = struct_type_field.into_inner();

                let field_type = parse_type(field_tokens.next().unwrap(), file_name)?;
                let field_name = parse_ident(field_tokens.next().unwrap(), file_name)?;
                assert!(field_tokens.next().is_none());

                fields.push((field_name, field_type));
            }

            constructor(fields)
        }
        Rule::named_type => Type::Typedef(type_token.as_str()),
        rule => {
            return Err(PestError::new_from_span(
                ErrorVariant::ParsingError {
                    positives: vec![
                        Rule::char_type,
                        Rule::int_type,
                        Rule::bool_type,
                        Rule::void_type,
                        Rule::struct_type,
                        Rule::named_type,
                    ],
                    negatives: vec![rule],
                },
                type_token.as_span(),
            ));
        }
    };

    let wrapper = |it, next_span| {
        Type::SpannedType(
            Box::new(it),
            AnnotatedSpan {
                span: merge_pest_spans(span, next_span).unwrap(),
                file_name,
            },
        )
    };

    tokens.fold(Ok((wrapper)(parsed_type, span)), |acc, next| {
        let next_span = next.as_span();
        let next_type = match next.as_rule() {
            Rule::pointer_type_mod => Type::Pointer(acc?.into()),
            Rule::array_type_mod => Type::Array(
                acc?.into(),
                parse_number(next.into_inner().next().unwrap())?,
            ),
            rule => {
                return Err(PestError::new_from_span(
                    ErrorVariant::ParsingError {
                        positives: vec![Rule::pointer_type_mod, Rule::array_type_mod],
                        negatives: vec![rule],
                    },
                    next.as_span(),
                ));
            }
        };

        Ok((wrapper)(next_type, next_span))
    })
}

fn parse_ident<'a>(pair: Pair<'a, Rule>, _file_name: &'a str) -> Result<IdentRef<'a>> {
    if !matches!(pair.as_rule(), Rule::ident) {
        return Err(PestError::new_from_span(
            ErrorVariant::ParsingError {
                positives: vec![Rule::ident],
                negatives: vec![pair.as_rule()],
            },
            pair.as_span(),
        ));
    }

    Ok(pair.as_str())
}

fn parse_expr<'a>(pairs: Pairs<'a, Rule>, file_name: &'a str) -> Result<Expr<'a>> {
    PRATT_PARSER
        .map_primary(|primary| {
            let span = primary.as_span();
            let span = AnnotatedSpan { span, file_name };

            // Handle primary expressions (atoms)
            match primary.as_rule() {
                Rule::value => Ok(Expr::Value(parse_value(primary)?, span)),
                Rule::ident => Ok(Expr::Variable(
                    parse_ident(primary, file_name)?,
                    DeferedVersion::UnresolvedVersion,
                    span,
                )),
                Rule::expression => {
                    // Parenthesized expression
                    Ok(parse_expr(primary.into_inner(), file_name)?)
                }
                Rule::function_call => {
                    Ok(Expr::FunctionCall(parse_function_call(primary, file_name)?))
                }
                Rule::global_builtin => {
                    // Ok(Expr::Global(
                    //     parse_type(primary.into_inner().next().unwrap(), file_name)?.into(),
                    //     DeferedAddress::UnresolvedAddress,
                    //     span,
                    // ))
                    let inner = primary.clone().into_inner().next().unwrap();
                    match inner.as_rule() {
                        Rule::var_type => Ok(Expr::GlobalOfType(
                            parse_type(primary.into_inner().next().unwrap(), file_name)?.into(),
                            DeferedAddress::UnresolvedAddress,
                            span,
                        )),
                        Rule::expression => Ok(Expr::GlobalOfExpr(
                            parse_expr(primary.into_inner(), file_name)?.into(),
                            span,
                        )),
                        rule => {
                            return Err(PestError::new_from_span(
                                ErrorVariant::ParsingError {
                                    positives: vec![Rule::var_type, Rule::expression],
                                    negatives: vec![rule],
                                },
                                inner.as_span(),
                            ));
                        }
                    }
                }
                Rule::box_builtin => Ok(Expr::Box(
                    parse_expr(primary.into_inner(), file_name)?.into(),
                    DeferedType::UnresolvedType,
                    span,
                )),
                Rule::sizeof_builtin => {
                    let inner = primary.clone().into_inner().next().unwrap();
                    match inner.as_rule() {
                        Rule::var_type => Ok(Expr::SizeOfType(
                            parse_type(inner, file_name)?,
                            SizeOfMode::Native,
                            span,
                        )),
                        Rule::expression => Ok(Expr::SizeOfExpr(
                            parse_expr(inner.into_inner(), file_name)?.into(),
                            DeferedType::UnresolvedType,
                            SizeOfMode::Native,
                            span,
                        )),
                        rule => {
                            return Err(PestError::new_from_span(
                                ErrorVariant::ParsingError {
                                    positives: vec![Rule::var_type, Rule::expression],
                                    negatives: vec![rule],
                                },
                                inner.as_span(),
                            ));
                        }
                    }
                }
                Rule::sizeof_packed_builtin => {
                    let inner = primary.clone().into_inner().next().unwrap();
                    match inner.as_rule() {
                        Rule::var_type => Ok(Expr::SizeOfType(
                            parse_type(inner, file_name)?,
                            SizeOfMode::Packed,
                            span,
                        )),
                        Rule::expression => Ok(Expr::SizeOfExpr(
                            parse_expr(inner.into_inner(), file_name)?.into(),
                            DeferedType::UnresolvedType,
                            SizeOfMode::Packed,
                            span,
                        )),
                        rule => {
                            return Err(PestError::new_from_span(
                                ErrorVariant::ParsingError {
                                    positives: vec![Rule::var_type, Rule::expression],
                                    negatives: vec![rule],
                                },
                                inner.as_span(),
                            ));
                        }
                    }
                }
                Rule::line_builtin => Ok(Expr::Value(
                    Value::Int(span.span.start_pos().line_col().0 as ClacValue),
                    span,
                )),
                Rule::if_statement => Ok(Expr::If(parse_if_expr(primary, file_name)?)),
                Rule::struct_expr => {
                    let mut struct_expr_fields = primary.into_inner();
                    let mut fields = Vec::new();

                    let constructor: &dyn Fn(_) -> _ = if struct_expr_fields
                        .peek()
                        .map(|it| it.as_rule() == Rule::struct_kind)
                        .unwrap_or(false)
                    {
                        let kind = struct_expr_fields
                            .next()
                            .unwrap()
                            .into_inner()
                            .next()
                            .unwrap();

                        match kind.as_rule() {
                            Rule::struct_kind_inorder => &|fields| {
                                Expr::NamedTuple(fields, DeferedType::UnresolvedType, span)
                            },
                            rule => {
                                return Err(PestError::new_from_span(
                                    ErrorVariant::ParsingError {
                                        positives: vec![Rule::struct_kind_inorder],
                                        negatives: vec![rule],
                                    },
                                    kind.as_span(),
                                ));
                            }
                        }
                    } else {
                        &|fields| {
                            Expr::Struct(
                                fields.into_iter().collect(),
                                DeferedType::UnresolvedType,
                                span,
                            )
                        }
                    };

                    for struct_value_field in struct_expr_fields {
                        let mut field_tokens = struct_value_field.into_inner();

                        let field_name = parse_ident(field_tokens.next().unwrap(), file_name)?;
                        let field_expr =
                            parse_expr(field_tokens.next().unwrap().into_inner(), file_name)?;
                        assert!(field_tokens.next().is_none());

                        fields.push((field_name, field_expr));
                    }

                    Ok(constructor(fields))
                }
                Rule::array_expr => {
                    let array_exprs = primary.into_inner();
                    let mut exprs = Vec::new();

                    for array_value_field in array_exprs {
                        let expr = parse_expr(array_value_field.into_inner(), file_name)?;

                        exprs.push(expr);
                    }

                    Ok(Expr::Array(exprs, DeferedType::UnresolvedType, span))
                }
                rule => {
                    return Err(PestError::new_from_span(
                        ErrorVariant::ParsingError {
                            positives: vec![
                                Rule::value,
                                Rule::ident,
                                Rule::function_call,
                                Rule::sizeof_builtin,
                                Rule::sizeof_packed_builtin,
                                Rule::line_builtin,
                                Rule::if_statement,
                                Rule::struct_expr,
                                Rule::array_expr,
                            ],
                            negatives: vec![rule],
                        },
                        primary.as_span(),
                    ));
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
                rule => {
                    return Err(PestError::new_from_span(
                        ErrorVariant::ParsingError {
                            positives: vec![
                                Rule::add,
                                Rule::subtract,
                                Rule::multiply,
                                Rule::divide,
                                Rule::modulo,
                                Rule::eq,
                                Rule::ne,
                                Rule::le,
                                Rule::ge,
                                Rule::lt,
                                Rule::gt,
                                Rule::logical_and,
                                Rule::logical_or,
                                Rule::shr,
                                Rule::shl,
                                Rule::bit_and,
                            ],
                            negatives: vec![rule],
                        },
                        op.as_span(),
                    ));
                }
            };

            let lhs = lhs?;
            let rhs = rhs?;
            let op_span = AnnotatedSpan {
                span: op.as_span(),
                file_name,
            };
            let span = merge_spans(&op_span, &rhs.as_span()).unwrap_or(op_span);
            let span = merge_spans(&span, &lhs.as_span()).unwrap_or(span);

            Ok(Expr::BinaryOp {
                op: bin_op,
                left: Box::new(lhs),
                right: Box::new(rhs),
                span,
                op_span: op_span,
                left_type: DeferedType::UnresolvedType,
                right_type: DeferedType::UnresolvedType,
            })
        })
        .map_prefix(|op, rhs| {
            // Handle unary operations
            let pre_op = match op.as_rule() {
                Rule::cast => PrefixOp::Cast(parse_type(
                    op.clone().into_inner().next().unwrap(),
                    file_name,
                )?),
                Rule::dereference => PrefixOp::Dereference,
                Rule::addrs_of => PrefixOp::AddressOf,
                Rule::negate => PrefixOp::Negate,
                Rule::invert => PrefixOp::Invert,
                Rule::logical_not => PrefixOp::LNot,
                rule => {
                    return Err(PestError::new_from_span(
                        ErrorVariant::ParsingError {
                            positives: vec![
                                Rule::cast,
                                Rule::dereference,
                                Rule::addrs_of,
                                Rule::negate,
                                Rule::invert,
                                Rule::logical_not,
                            ],
                            negatives: vec![rule],
                        },
                        op.as_span(),
                    ));
                }
            };

            let rhs = rhs?;
            let op_span = AnnotatedSpan {
                span: op.as_span(),
                file_name,
            };
            let span = merge_spans(&op_span, &rhs.as_span()).unwrap_or(op_span);

            Ok(Expr::PrefixOp {
                op: pre_op,
                operand: Box::new(rhs),
                span,
                op_span,
                operand_type: DeferedType::UnresolvedType,
            })
        })
        .map_postfix(|lhs, op| {
            let post_op = match op.as_rule() {
                Rule::member => PostfixOp::Member(parse_ident(
                    op.clone().into_inner().next().unwrap(),
                    file_name,
                )?),
                Rule::member_deref => PostfixOp::MemberDeref(parse_ident(
                    op.clone().into_inner().next().unwrap(),
                    file_name,
                )?),
                Rule::array_idx => {
                    PostfixOp::ArrayIndex(parse_expr(op.clone().into_inner(), file_name)?.into())
                }
                rule => {
                    return Err(PestError::new_from_span(
                        ErrorVariant::ParsingError {
                            positives: vec![Rule::member, Rule::member_deref, Rule::array_idx],
                            negatives: vec![rule],
                        },
                        op.as_span(),
                    ));
                }
            };

            let lhs = lhs?;
            let op_span = AnnotatedSpan {
                span: op.as_span(),
                file_name,
            };
            let span = merge_spans(&op_span, &lhs.as_span()).unwrap_or(op_span);

            Ok(Expr::PostfixOp {
                op: post_op,
                operand: Box::new(lhs),
                span,
                op_span,
                operand_type: DeferedType::UnresolvedType,
            })
        })
        .parse(pairs)
}

fn parse_function_call<'a>(pair: Pair<'a, Rule>, file_name: &'a str) -> Result<FunctionCall<'a>> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    let function = parse_ident(inner.next().unwrap(), file_name)?;

    Ok(FunctionCall {
        function,
        parameters: inner
            .map(|it| it.into_inner())
            .map(|it| parse_expr(it, file_name))
            .collect::<Result<_>>()?,
        span: AnnotatedSpan { span, file_name },
    })
}

fn parse_number<'a>(pair: Pair<'a, Rule>) -> Result<ClacValue> {
    let res = parse_int::parse::<ClacValueUnsigned>(pair.as_str());

    match res {
        Ok(val) => Ok(val as ClacValue),
        Err(err) => Err(PestError::new_from_span(
            ErrorVariant::CustomError {
                message: format!("Failed to parse number `{}`, due to {err}", pair.as_str()),
            },
            pair.as_span(),
        )),
    }
}

fn parse_bool<'a>(pair: Pair<'a, Rule>) -> Result<bool> {
    let res = pair.as_str().parse::<bool>();

    match res {
        Ok(val) => Ok(val),
        Err(err) => Err(PestError::new_from_span(
            ErrorVariant::CustomError {
                message: format!("Failed to parse bool `{}`, due to {err}", pair.as_str()),
            },
            pair.as_span(),
        )),
    }
}

fn handle_escapes(str: &str) -> Cow<'_, str> {
    str.replace("\\n", "\n")
        .replace("\\r", "\r")
        .replace("\\t", "\t")
        .replace("\\0", "\0")
        .into()
}

fn parse_string<'a>(pair: Pair<'a, Rule>) -> Result<Cow<'a, str>> {
    Ok(handle_escapes(pair.into_inner().next().unwrap().as_str()))
}

fn parse_char<'a>(pair: Pair<'a, Rule>) -> Result<ClacValue> {
    let literal = pair.as_str();
    let span = pair.as_span();
    let str = handle_escapes(pair.into_inner().next().unwrap().as_str());

    match str.as_bytes() {
        &[] => Err(PestError::new_from_span(
            ErrorVariant::CustomError {
                message: format!("Empty char literal `{}`", literal),
            },
            span,
        )),
        &[char] => Ok(char.into()),
        &[..] => Err(PestError::new_from_span(
            ErrorVariant::CustomError {
                message: format!("Over sized char literal `{}`", literal),
            },
            span,
        )),
    }
}

fn parse_value<'a>(pair: Pair<'a, Rule>) -> Result<Value<'a>> {
    let target = pair.into_inner().next().unwrap();

    match target.as_rule() {
        Rule::number => Ok(Value::Int(parse_number(target)?)),
        Rule::boolean => Ok(Value::Bool(parse_bool(target)?)),
        Rule::char => Ok(Value::Char(parse_char(target)?)),
        Rule::string => Ok(Value::String(parse_string(target)?)),
        rule => {
            return Err(PestError::new_from_span(
                ErrorVariant::ParsingError {
                    positives: vec![Rule::number, Rule::boolean, Rule::char, Rule::string],
                    negatives: vec![rule],
                },
                target.as_span(),
            ));
        }
    }
}
