use std::{collections::HashMap, sync::Arc};

use crate::{
    ast::{IdentRef, Type},
    codegen::{
        clac::{ClacToken, MangledIdent},
        ir::FunctionSignature,
    },
};

pub struct ClacBuiltin {}

pub fn clac_builtins() -> HashMap<IdentRef<'static>, (ClacToken, FunctionSignature<'static>)> {
    let mut map = HashMap::new();

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
            ClacToken::Call {
                mangled_ident: MangledIdent(Arc::new("syscall".to_string())),
                stack_delta: -6,
            },
            FunctionSignature {
                arguements: vec![
                    (Type::Int, "v6"),
                    (Type::Int, "v5"),
                    (Type::Int, "v4"),
                    (Type::Int, "v3"),
                    (Type::Int, "v2"),
                    (Type::Int, "v1"),
                    (Type::Int, "rax"),
                ],
                return_type: Type::Int,
            },
        ),
    );

    map.insert(
        "write8",
        (
            ClacToken::Call {
                mangled_ident: MangledIdent(Arc::new("syscall".to_string())),
                stack_delta: -2,
            },
            FunctionSignature {
                arguements: vec![(Type::Int, "val"), (Type::Int, "addr")],
                return_type: Type::Void,
            },
        ),
    );

    map.insert(
        "writeNative",
        (
            ClacToken::Call {
                mangled_ident: MangledIdent(Arc::new("syscall".to_string())),
                stack_delta: -2,
            },
            FunctionSignature {
                arguements: vec![(Type::Int, "val"), (Type::Int, "addr")],
                return_type: Type::Void,
            },
        ),
    );

    map.insert(
        "read8",
        (
            ClacToken::Call {
                mangled_ident: MangledIdent(Arc::new("syscall".to_string())),
                stack_delta: 0,
            },
            FunctionSignature {
                arguements: vec![(Type::Int, "addr")],
                return_type: Type::Int,
            },
        ),
    );

    map.insert(
        "readNative",
        (
            ClacToken::Call {
                mangled_ident: MangledIdent(Arc::new("syscall".to_string())),
                stack_delta: 0,
            },
            FunctionSignature {
                arguements: vec![(Type::Int, "addr")],
                return_type: Type::Int,
            },
        ),
    );

    map
}
