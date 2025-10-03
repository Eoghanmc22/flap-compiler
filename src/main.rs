#![feature(push_mut)]

use std::{
    ffi::OsStr,
    fs::{self, File, OpenOptions},
    io::Write,
    path::PathBuf,
};

use anyhow::Context;
use clap::Parser;

use crate::codegen::CodegenCtx;

pub mod ast;
pub mod codegen;
pub mod middleware;
pub mod parser;

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

fn main() -> anyhow::Result<()> {
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

fn compile(file: PathBuf) -> anyhow::Result<()> {
    let contents = fs::read_to_string(&file).context("Read file")?;

    let program = parser::parse_program(&contents).context("Parse program")?;
    println!("Parsed AST: {program:#?}");

    let mut ctx = CodegenCtx::default();
    middleware::walk_block(&mut ctx, &program).context("Ast to Clac")?;

    let output_dir = PathBuf::from("out/");
    fs::create_dir_all(&output_dir).context("Create out dir")?;
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
        .context("Open output file")?;
    write!(&mut file, "{ctx}").context("Write code")?;

    Ok(())
}
