use clap::Parser;
use cranegen::Compiler;
use cst::Cst;
use std::{env, fs, path::PathBuf, process::Command, str::FromStr};

use tokenise::tokenize_all;
mod cst;

mod cranegen;
mod tokenise;

#[derive(Parser)]
#[command(version, about = "Compiler for the act language", long_about = None)]
struct Args {
    #[arg(short, long, help = "The .act source file to compile")]
    file: String,
    #[arg(
        short,
        long,
        help = "Whether to debug the compiled functions by dumping their IR format"
    )]
    debug: bool,
}

fn main() {
    if let Err(e) = compile() {
        println!("{e}");
    }
}

fn compile() -> Result<(), String> {
    let args = Args::parse();
    let path = PathBuf::from_str(&args.file).map_err(|_| "Could not parse file name")?;
    let stem = path
        .file_stem()
        .ok_or("Could not get file stem from given file name")?
        .to_string_lossy();
    let extension = path
        .extension()
        .ok_or("Could not get file extension from given file name")?
        .to_string_lossy();

    if &extension != "act" {
        Err("Input file must have extenstion 'act', passed file has extension '{extension}'")?
    }

    let input: Vec<char> = fs::read_to_string(&path)
        .expect(&format!("No such file {}", &args.file))
        .chars()
        .collect();

    let tokenised = tokenize_all(input.as_slice()).ok_or("Error tokenising")?;
    let tree = cst::parse(&tokenised).map_err(|e| format!("Error parsing: {e:?}"))?;

    gen_cranelift(tree, args.debug, &format!("{stem}.o"))?;

    let home = env::var("HOME").unwrap();

    Command::new("gcc")
        .arg("-o")
        .arg(stem.to_string())
        .arg(&format!("{stem}.o"))
        .arg(format!("{home}/.local/lib/libactrt.a"))
        .spawn()
        .map_err(|_| "It seems you do not have GCC installed".to_string())
        .map(|_| ())
}

fn gen_cranelift(instrs: Cst, debug: bool, name: &str) -> Result<(), String> {
    let mut compiler = Compiler::default();

    compiler.debug = debug;

    compiler
        .compile(instrs)
        .map_err(|e| format!("Code generation error: {}", e.to_string()))?;
    compiler.finish(name);
    Ok(())
}
