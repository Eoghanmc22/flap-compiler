use std::collections::HashMap;

use crate::{
    ast::{
        AnnotatedSpan, Arguement, Captures, DeferedCaptures, DeferedVersion, FunctionSignature,
        IdentRef, Type,
    },
    codegen::clac::ClacToken,
};

pub struct ClacBuiltin {}

pub fn clac_builtins() -> HashMap<IdentRef<'static>, (ClacToken, FunctionSignature<'static>)> {
    let mut map = HashMap::new();
    let v = DeferedVersion::UnresolvedVersion;

    map.insert(
        "pow",
        (
            ClacToken::Pow,
            FunctionSignature {
                arguements: vec![
                    Arguement {
                        arg_type: Type::Int,
                        arg_name: "base",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                    Arguement {
                        arg_type: Type::Int,
                        arg_name: "power",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                ],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Int,
                span: AnnotatedSpan::builtin(),
            },
        ),
    );

    map.insert(
        "print",
        (
            ClacToken::Print,
            FunctionSignature {
                arguements: vec![Arguement {
                    arg_type: Type::Int,
                    arg_name: "value",
                    version: v,
                    span: AnnotatedSpan::builtin(),
                }],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Void,
                span: AnnotatedSpan::builtin(),
            },
        ),
    );

    map.insert(
        "print_bool",
        (
            ClacToken::Print,
            FunctionSignature {
                arguements: vec![Arguement {
                    arg_type: Type::Bool,
                    arg_name: "value",
                    version: v,
                    span: AnnotatedSpan::builtin(),
                }],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Void,
                span: AnnotatedSpan::builtin(),
            },
        ),
    );

    map.insert(
        "quit",
        (
            ClacToken::Quit,
            FunctionSignature {
                arguements: vec![],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Void,
                span: AnnotatedSpan::builtin(),
            },
        ),
    );

    map.insert(
        "syscall",
        (
            ClacToken::Syscall,
            FunctionSignature {
                arguements: vec![
                    Arguement {
                        arg_type: Type::Int,
                        arg_name: "rax",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                    Arguement {
                        arg_type: Type::Int,
                        arg_name: "v1",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                    Arguement {
                        arg_type: Type::Int,
                        arg_name: "v2",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                    Arguement {
                        arg_type: Type::Int,
                        arg_name: "v3",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                    Arguement {
                        arg_type: Type::Int,
                        arg_name: "v5",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                    Arguement {
                        arg_type: Type::Int,
                        arg_name: "v4",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                    Arguement {
                        arg_type: Type::Int,
                        arg_name: "v6",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                ],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Int,
                span: AnnotatedSpan::builtin(),
            },
        ),
    );

    map.insert(
        "write8",
        (
            ClacToken::Write8,
            FunctionSignature {
                arguements: vec![
                    Arguement {
                        arg_type: Type::Pointer(Type::Char.into()),
                        arg_name: "addr",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                    Arguement {
                        arg_type: Type::Char,
                        arg_name: "val",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                ],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Void,
                span: AnnotatedSpan::builtin(),
            },
        ),
    );

    map.insert(
        "write_native",
        (
            ClacToken::WriteNative,
            FunctionSignature {
                arguements: vec![
                    Arguement {
                        arg_type: Type::Pointer(Type::Int.into()),
                        arg_name: "addr",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                    Arguement {
                        arg_type: Type::Int,
                        arg_name: "val",
                        version: v,
                        span: AnnotatedSpan::builtin(),
                    },
                ],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Void,
                span: AnnotatedSpan::builtin(),
            },
        ),
    );

    map.insert(
        "read8",
        (
            ClacToken::Read8,
            FunctionSignature {
                arguements: vec![Arguement {
                    arg_type: Type::Pointer(Type::Char.into()),
                    arg_name: "addr",
                    version: v,
                    span: AnnotatedSpan::builtin(),
                }],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Char,
                span: AnnotatedSpan::builtin(),
            },
        ),
    );

    map.insert(
        "read_native",
        (
            ClacToken::ReadNative,
            FunctionSignature {
                arguements: vec![Arguement {
                    arg_type: Type::Pointer(Type::Int.into()),
                    arg_name: "addr",
                    version: v,
                    span: AnnotatedSpan::builtin(),
                }],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Int,
                span: AnnotatedSpan::builtin(),
            },
        ),
    );

    map.insert(
        "int_bit_width",
        (
            ClacToken::WidthNative,
            FunctionSignature {
                arguements: vec![],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Int,
                span: AnnotatedSpan::builtin(),
            },
        ),
    );

    map
}
