use std::collections::HashMap;

use crate::{
    ast::{IdentRef, Type},
    codegen::{clac::ClacToken, ir::FunctionSignature},
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

    map
}
