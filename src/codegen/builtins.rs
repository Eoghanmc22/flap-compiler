use std::collections::HashMap;

use crate::{
    ast::{Captures, DeferedCaptures, DeferedVersion, FunctionSignature, IdentRef, Type},
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
                arguements: vec![(Type::Int, "base", v), (Type::Int, "power", v)],
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
                arguements: vec![(Type::Int, "value", v)],
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
                arguements: vec![(Type::Bool, "value", v)],
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
                    (Type::Int, "rax", v),
                    (Type::Int, "v1", v),
                    (Type::Int, "v2", v),
                    (Type::Int, "v3", v),
                    (Type::Int, "v5", v),
                    (Type::Int, "v4", v),
                    (Type::Int, "v6", v),
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
                    (Type::Pointer(Type::Char.into()), "addr", v),
                    (Type::Char, "val", v),
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
                    (Type::Pointer(Type::Int.into()), "addr", v),
                    (Type::Int, "val", v),
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
                arguements: vec![(Type::Pointer(Type::Char.into()), "addr", v)],
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
                arguements: vec![(Type::Pointer(Type::Int.into()), "addr", v)],
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
