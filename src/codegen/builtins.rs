use std::collections::HashMap;

use crate::{
    ast::{FunctionSignature, IdentRef, Type},
    codegen::clac::ClacToken,
};

pub struct ClacBuiltin {}

pub fn clac_builtins() -> HashMap<IdentRef<'static>, (ClacToken, FunctionSignature<'static>)> {
    let mut map = HashMap::new();

    map.insert(
        "pow",
        (
            ClacToken::Pow,
            FunctionSignature {
                arguements: vec![(Type::Int, "base"), (Type::Int, "power")],
                return_type: Type::Int,
            },
        ),
    );

    map.insert(
        "print",
        (
            ClacToken::Print,
            FunctionSignature {
                arguements: vec![(Type::Int, "value")],
                return_type: Type::Void,
            },
        ),
    );

    map.insert(
        "print_bool",
        (
            ClacToken::Print,
            FunctionSignature {
                arguements: vec![(Type::Bool, "value")],
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
                    (Type::Int, "rax"),
                    (Type::Int, "v1"),
                    (Type::Int, "v2"),
                    (Type::Int, "v3"),
                    (Type::Int, "v5"),
                    (Type::Int, "v4"),
                    (Type::Int, "v6"),
                ],
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
                    (Type::Pointer(Type::Char.into()), "addr"),
                    (Type::Char, "val"),
                ],
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
                    (Type::Pointer(Type::Int.into()), "addr"),
                    (Type::Int, "val"),
                ],
                return_type: Type::Void,
            },
        ),
    );

    map.insert(
        "read8",
        (
            ClacToken::Read8,
            FunctionSignature {
                arguements: vec![(Type::Pointer(Type::Char.into()), "addr")],
                return_type: Type::Char,
            },
        ),
    );

    map.insert(
        "read_native",
        (
            ClacToken::ReadNative,
            FunctionSignature {
                arguements: vec![(Type::Pointer(Type::Int.into()), "addr")],
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
                return_type: Type::Int,
            },
        ),
    );

    map
}
