use std::collections::HashMap;

use crate::{
    ast::{
        AnnotatedSpan, Captures, DeferedCaptures, DeferedVersion, FunctionSignature, IdentRef, Type,
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
                    (Type::Int, "base", v, AnnotatedSpan::builtin()),
                    (Type::Int, "power", v, AnnotatedSpan::builtin()),
                ],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Int,
            },
        ),
    );

    map.insert(
        "print",
        (
            ClacToken::Print,
            FunctionSignature {
                arguements: vec![(Type::Int, "value", v, AnnotatedSpan::builtin())],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Void,
            },
        ),
    );

    map.insert(
        "print_bool",
        (
            ClacToken::Print,
            FunctionSignature {
                arguements: vec![(Type::Bool, "value", v, AnnotatedSpan::builtin())],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Void,
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
            },
        ),
    );

    map.insert(
        "syscall",
        (
            ClacToken::Syscall,
            FunctionSignature {
                arguements: vec![
                    (Type::Int, "rax", v, AnnotatedSpan::builtin()),
                    (Type::Int, "v1", v, AnnotatedSpan::builtin()),
                    (Type::Int, "v2", v, AnnotatedSpan::builtin()),
                    (Type::Int, "v3", v, AnnotatedSpan::builtin()),
                    (Type::Int, "v5", v, AnnotatedSpan::builtin()),
                    (Type::Int, "v4", v, AnnotatedSpan::builtin()),
                    (Type::Int, "v6", v, AnnotatedSpan::builtin()),
                ],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Int,
            },
        ),
    );

    map.insert(
        "write8",
        (
            ClacToken::Write8,
            FunctionSignature {
                arguements: vec![
                    (
                        Type::Pointer(Type::Char.into()),
                        "addr",
                        v,
                        AnnotatedSpan::builtin(),
                    ),
                    (Type::Char, "val", v, AnnotatedSpan::builtin()),
                ],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Void,
            },
        ),
    );

    map.insert(
        "write_native",
        (
            ClacToken::WriteNative,
            FunctionSignature {
                arguements: vec![
                    (
                        Type::Pointer(Type::Int.into()),
                        "addr",
                        v,
                        AnnotatedSpan::builtin(),
                    ),
                    (Type::Int, "val", v, AnnotatedSpan::builtin()),
                ],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Void,
            },
        ),
    );

    map.insert(
        "read8",
        (
            ClacToken::Read8,
            FunctionSignature {
                arguements: vec![(
                    Type::Pointer(Type::Char.into()),
                    "addr",
                    v,
                    AnnotatedSpan::builtin(),
                )],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Char,
            },
        ),
    );

    map.insert(
        "read_native",
        (
            ClacToken::ReadNative,
            FunctionSignature {
                arguements: vec![(
                    Type::Pointer(Type::Int.into()),
                    "addr",
                    v,
                    AnnotatedSpan::builtin(),
                )],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Int,
            },
        ),
    );

    map.insert(
        "int_width",
        (
            ClacToken::WidthNative,
            FunctionSignature {
                arguements: vec![],
                captures: DeferedCaptures::ResolvedCaptures(Captures::default()),
                return_type: Type::Int,
            },
        ),
    );

    map
}
