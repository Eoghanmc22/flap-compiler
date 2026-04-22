#![feature(try_blocks)]
#![feature(try_blocks_heterogeneous)]
#![feature(coroutines)]
#![feature(iter_from_coroutine)]
#![feature(error_generic_member_access)]
#![feature(int_roundings)]

pub mod ast;
pub mod codegen;
pub mod compile;
pub mod error;
pub mod lsp;
pub mod middleware;
pub mod parser;
pub mod type_check;
