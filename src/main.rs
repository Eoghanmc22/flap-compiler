// TODO:
// - reenable nested function defs
// - unify functions and builtins
//   - get rid of the special builtins map
//   - support inligning regular functions
//   - DO this by replacing the mangledident thing with an enum that can either be a mangled ident
//   or a vector of clac tokens
// - Add structs and arrays
//   - make a drop range builtin
// - Make an optimization for tail recursion
//   - We should drop everything but the arguements to the call if a function is the last thing
//   called in a block
// - Constants should be allowed to have expressions
// - Structs, tuples, arrays
// - Name spaces and file imports
// - Make the debug output chill out
// - The source code comments dont seem to work any more
#![feature(push_mut)]

use std::{
    ffi::OsStr,
    fs::{self, OpenOptions},
    io::Write,
    path::PathBuf,
};

use clap::Parser;
use color_eyre::eyre::{Context, Result};

use crate::{
    codegen::{
        CodegenCtx,
        post_process::{
            AttributionPostProcessor, ExtractDefinitionsPostProcessor, PostProcesser,
            SourceCodeCommentPostProcessor,
        },
    },
    type_check::{TypeCheck, TypeChecker},
};

pub mod ast;
pub mod codegen;
pub mod middleware;
pub mod parser;
pub mod type_check;

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(clap::Subcommand)]
enum Commands {
    Compile { files: Vec<PathBuf> },
}

fn main() -> Result<()> {
    color_eyre::install()?;

    let cli = Cli::parse();

    println!("Hello, world!");
    match cli.command {
        Commands::Compile { files } => {
            for file in files {
                println!("Compiling {file:?}");
                compile(file)?;
            }
        }
    }

    Ok(())
}

fn compile(file: PathBuf) -> Result<()> {
    let source_code = fs::read_to_string(&file).wrap_err("Read file")?;

    let mut program = parser::parse_program(&source_code).wrap_err("Parse program")?;
    println!("Parsed AST: {program:#?}");

    let mut type_checker = TypeChecker::default();
    let return_type = program
        .check_and_resolve_types(&mut type_checker)
        .wrap_err("Type Check Program")?;

    let mut codegen = CodegenCtx::default();
    let tail_expr = middleware::walk_block(&mut codegen, &program).wrap_err("Ast to Clac")?;
    codegen
        .bring_up_references(&[tail_expr], return_type.width())
        .wrap_err("Bring up tail expr")?;

    let mut program = codegen.into_tokens();

    let post_processors: [&mut dyn PostProcesser; _] = [
        &mut ExtractDefinitionsPostProcessor,
        &mut SourceCodeCommentPostProcessor(&source_code),
        &mut AttributionPostProcessor,
    ];
    for post_processor in post_processors {
        post_processor.process(&mut program);
    }

    let output_dir = PathBuf::from("out/");
    fs::create_dir_all(&output_dir).wrap_err("Create out dir")?;
    let out_file = output_dir.join(
        file.with_extension("clac")
            .file_name()
            .unwrap_or(OsStr::new("out.clac")),
    );

    let mut file = OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(out_file)
        .wrap_err("Open output file")?;
    write!(&mut file, "{program}").wrap_err("Write code")?;

    Ok(())
}
