use std::{fs, path::PathBuf};

use anyhow::Context;
use clap::Parser;

pub mod ast;
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

    Ok(())
}
