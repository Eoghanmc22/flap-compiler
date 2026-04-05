// TODO:
// - I dont think logical and and or are short circuiting
// - support inlining regular functions?
// - Name spaces and methods
// - Things that should be toggale
//   - Source code comment
// - Add data flow analysis and instruction reordering
// - reduce clone/to_string/to_vec/... usage
#![feature(try_blocks)]

use std::{path::PathBuf, thread, time::Instant};

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
    Compile {
        #[arg(long)]
        no_parallel: bool,
        files: Vec<PathBuf>,
    },
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
        Commands::Compile { files, no_parallel } => {
            if !no_parallel {
                thread::scope(|spawner| -> Result<()> {
                    let mut handles = Vec::new();

                    for file in files {
                        let handle = spawner.spawn(move || -> Result<()> {
                            info!("Compiling {file:?}");
                            compile::compile(&file)?;
                            info!("Finished {file:?}");

                            Ok(())
                        });

                        handles.push(handle);
                    }

                    for handle in handles {
                        handle.join().unwrap()?;
                    }

                    Ok(())
                })?;
            } else {
                info!("Compiling without parallelism");
                for file in files {
                    info!("Compiling {file:?}");
                    compile::compile(&file)?;
                }
            }
        }
    }
    info!("Done in {:.2}s!", start.elapsed().as_secs_f64());

    Ok(())
}
