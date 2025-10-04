// TODO: figure out where to run the good type checking
// TODO: type inference for local vars
// TODO: Need to add back semicolons so that we know when an implicit return is desired
#![feature(push_mut)]

use std::{
    ffi::OsStr,
    fs::{self, OpenOptions},
    io::Write,
    path::PathBuf,
};

use clap::Parser;
use color_eyre::eyre::{Context, Result};

use crate::codegen::CodegenCtx;

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
    let contents = fs::read_to_string(&file).wrap_err("Read file")?;

    let program = parser::parse_program(&contents).wrap_err("Parse program")?;
    println!("Parsed AST: {program:#?}");

    let mut ctx = CodegenCtx::default();
    middleware::walk_block(&mut ctx, &program).wrap_err("Ast to Clac")?;

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
    write!(&mut file, "{ctx}").wrap_err("Write code")?;

    Ok(())
}
