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
// - Use Skip instead of If for conditionals in code gen
// - Stanley's syscall extensions
// - reduce clone/to_string/to_vec/... usage
// Consider making pointer assignment an expression
// Pointer arithmetic
#![feature(try_blocks)]

use std::{path::PathBuf, time::Instant};

use clap::Parser;
use color_eyre::eyre::Result;
use tracing::{info, level_filters::LevelFilter};
use tracing_error::ErrorLayer;
use tracing_subscriber::{EnvFilter, prelude::*};

pub mod ast;
pub mod codegen;
pub mod compile;
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
                compile::compile(&file)?;
            }
        }
    }
    info!("Done in {:.2}s!", start.elapsed().as_secs_f64());

    Ok(())
}
