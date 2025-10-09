// TODO:
// - I dont think logical and and or are short circuiting
// - support inlining regular functions? (this doesnt play well with if)
// - Add structs and arrays
// - Structs, tuples, arrays
// - Name spaces and file imports
// - Cull unused builtins
// - Things that should be toggale
//   - Nested defs
//   - Source code comment
//   - use of drop_range for tail recursion (most important)
//   - tail recursion at large?
//   - returning types wider than 2 ints since that requires drop range
// - Add data flow analysis and instruction reordering
#![feature(push_mut, try_blocks)]

use std::{
    ffi::OsStr,
    fmt::Debug,
    fs::{self, OpenOptions},
    io::Write,
    path::{Path, PathBuf},
    time::Instant,
};

use clap::Parser;
use color_eyre::eyre::{Context, Result};
use tracing::{debug, info, instrument, level_filters::LevelFilter};
use tracing_error::ErrorLayer;
use tracing_subscriber::{EnvFilter, prelude::*};

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
    let subscriber = tracing_subscriber::Registry::default()
        .with(ErrorLayer::default())
        .with(
            tracing_subscriber::fmt::layer().with_filter(
                EnvFilter::builder()
                    .with_default_directive(LevelFilter::INFO.into())
                    .from_env()?,
            ),
        );
    tracing::subscriber::set_global_default(subscriber)?;

    color_eyre::install()?;

    let cli = Cli::parse();

    let start = Instant::now();
    info!("Starting flap to clac compiler");
    match cli.command {
        Commands::Compile { files } => {
            for file in files {
                info!("Compiling {file:?}");
                compile(&file)?;
            }
        }
    }
    info!("Done in {:.2}s!", start.elapsed().as_secs_f64());

    Ok(())
}

#[instrument]
fn compile(file: impl AsRef<Path> + Debug) -> Result<()> {
    let file = file.as_ref();
    let source_code = fs::read_to_string(&file).wrap_err("Read file")?;

    let mut program = parser::parse_program(&source_code).wrap_err("Parse program")?;
    debug!("Parsed AST: {program:#?}");

    let mut type_checker = TypeChecker::default();
    let return_type = program
        .check_and_resolve_types(&mut type_checker)
        .wrap_err("Type Check Program")?;

    let mut codegen = CodegenCtx::default();
    let tail_expr = middleware::walk_block(&mut codegen, &program).wrap_err("Ast to Clac")?;
    let tail_data_ref = tail_expr
        .into_data_ref(&mut codegen)
        .wrap_err("Get tail data ref")?;
    codegen
        .bring_up_references(&[tail_data_ref], return_type.width())
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
