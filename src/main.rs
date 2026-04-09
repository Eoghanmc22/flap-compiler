// TODO:
// - I dont think logical and and or are short circuiting
// - support inlining regular functions?
// - Name spaces and methods
// - Things that should be toggle
//   - Source code comment
// - Add data flow analysis and instruction reordering
// - reduce clone/to_string/to_vec/... usage
// - consider making loops return the value of their last expression on their last iteration?
//
// Missing Features:
// - Indexing into a stack array with a variable that is not comptime known
// - Partial Mutation of stack structs and arrays

use std::{
    fs,
    io::{self, Write},
    path::PathBuf,
    thread,
    time::Instant,
};

use clac_lang::types::{ClacState, ExecError};
use clap::Parser;
use color_eyre::eyre::{Context, Result};
use flap_compiler::{
    codegen::clac::ClacToken,
    compile::{self, CompileConfig},
    lsp,
};
use tracing::{error, info, level_filters::LevelFilter};
use tracing_error::ErrorLayer;
use tracing_subscriber::{EnvFilter, prelude::*};

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
        #[command(flatten)]
        config: CompileConfigArgs,
        files: Vec<PathBuf>,
    },
    Repl,
    Run {
        file: PathBuf,
        #[command(flatten)]
        config: CompileConfigArgs,

        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        _extra: Vec<String>,
    },
    Lsp,
}

#[derive(clap::Args, Clone)]
struct CompileConfigArgs {
    #[arg(long, short)]
    verbose: bool,

    #[arg(long)]
    no_tree_shaking: bool,

    #[arg(long)]
    no_width_assert: bool,

    #[arg(long)]
    no_source_comment: bool,

    #[arg(long)]
    no_attribution: bool,
}

impl From<CompileConfigArgs> for CompileConfig {
    fn from(value: CompileConfigArgs) -> Self {
        CompileConfig {
            verbose_parsing_errors: value.verbose,
            tree_shaking: !value.no_tree_shaking,
            emit_native_width_assert: !value.no_width_assert,
            emit_source_code_comment: !value.no_source_comment,
            emit_attribution_comment: !value.no_attribution,
        }
    }
}

fn main() -> Result<()> {
    let subscriber = tracing_subscriber::Registry::default()
        .with(ErrorLayer::default())
        .with(
            tracing_subscriber::fmt::layer()
                .with_writer(io::stderr)
                .with_filter(
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
        Commands::Compile {
            files,
            no_parallel,
            config,
        } => {
            info!("flap-compiler by Eoghanmc22");

            if !no_parallel {
                thread::scope(|spawner| -> Result<()> {
                    let mut handles = Vec::new();

                    for file in files {
                        let config = config.clone();
                        let handle = spawner.spawn(move || -> Result<()> {
                            info!("Compiling {file:?}");
                            compile::compile_to_file(&file, config.into())?;
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

                    let config = config.clone();
                    compile::compile(&file, config.into())?;
                }
            }
        }
        Commands::Repl => {
            let mut state = ClacState::default();

            info!("clac++ repl by stanleymw");

            loop {
                print!("clac++> ");
                io::stdout().flush().unwrap();

                let mut buf = String::new();
                io::stdin().read_line(&mut buf).unwrap();

                match state.execute_str(&buf) {
                    Err(ExecError::Quit) => break,
                    Err(err) => {
                        error!("Error: {err:?}");
                    }
                    Ok(()) => {}
                };

                println!("{:?}", state.stack)
            }
        }
        Commands::Run { file, config, .. } => {
            let mut state = ClacState::default();

            let res = if file.extension() == Some("flap".as_ref()) {
                info!("flap-compiler by Eoghanmc22");
                info!("clac++ interpreter by stanleymw");

                let program = compile::compile(&file, config.into())?;
                let program = program
                    .0
                    .iter()
                    .flat_map(ClacToken::as_clac_lang)
                    .collect::<Vec<_>>();

                state.execute_tokens(&program)

                // let program = compile::compile_to_string(&file)?;
                // state.execute_str(&program)
            } else if file.extension() == Some("clac".as_ref()) {
                let program = fs::read_to_string(file).wrap_err("Read input file")?;
                state.execute_str(&program)
            } else {
                error!("Error: unknown extension {:?}", file.extension());
                return Ok(());
            };

            match res {
                Ok(()) | Err(ExecError::Quit) => {}
                Err(err) => {
                    error!("Error: {err:?}");
                }
            }
        }
        Commands::Lsp => lsp::start_lsp()?,
    }
    info!("Done in {:.2}s!", start.elapsed().as_secs_f64());

    Ok(())
}
