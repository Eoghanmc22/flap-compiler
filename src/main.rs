#![feature(push_mut)]

use std::{
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
    Compile { file: PathBuf },
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    println!("Hello, world!");
    match cli.command {
        Commands::Compile { file } => compile(file)?,
    }

    Ok(())
}

fn compile(file: PathBuf) -> anyhow::Result<()> {
    let contents = fs::read_to_string(file).context("Read file")?;

    let program = parser::parse_program(&contents).context("Parse program")?;
    println!("Parsed AST: {program:#?}");

    let mut ctx = CodegenCtx::default();
    middleware::walk_block(&mut ctx, &program).context("Ast to Clac")?;

    let mut file = OpenOptions::new()
        .truncate(true)
        .write(true)
        .open("out.clac")
        .context("Open output file")?;
    write!(&mut file, "{ctx}").context("Write code")?;

    Ok(())
}
