#![feature(try_blocks)]
#![feature(coroutines)]
#![feature(iter_from_coroutine)]
#![feature(error_generic_member_access)]

pub mod ast;
pub mod codegen;
pub mod compile;
pub mod lsp;
pub mod middleware;
pub mod parser;
pub mod type_check;
