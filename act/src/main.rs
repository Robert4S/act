use clap::Parser;
use cranegen::Compiler;
use cst::Cst;
use std::{env, fs, path::PathBuf, process::Command, str::FromStr};

use tokenise::tokenize_all;
//mod codegen;
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
    let args = Args::parse();
    let path = PathBuf::from_str(&args.file).unwrap();
    let stem = path.file_stem().unwrap().to_string_lossy();
    //let asm_file = format!("{stem}.S");
    let extension = path.extension().unwrap().to_string_lossy();

    assert!(
        &extension == "act",
        "Input file must have extenstion 'act', passed file has extension '{extension}'"
    );

    let input: Vec<char> = fs::read_to_string(&path)
        .expect(&format!("No such file {}", &args.file))
        .chars()
        .collect();

    let tokenised = tokenize_all(input.as_slice()).expect("Error tokenising");
    let tree = cst::parse(&tokenised).expect("Error parsing");
    //let instructions = cst::gen_instructions(tree.clone());

    gen_cranelift(tree, args.debug, &format!("{stem}.o"));

    //let mut x = codegen::Context::new();
    //let s = x.to_code(instructions).expect("Codegen error");

    let home = env::var("HOME").unwrap();

    //fs::write(&asm_file, s).unwrap();
    Command::new("gcc")
        .arg("-o")
        .arg(stem.to_string())
        .arg(&format!("{stem}.o"))
        .arg(format!("{home}/.local/lib/libactrt.a"))
        .spawn()
        .expect("It seems you do not have GCC installed");
}

fn gen_cranelift(instrs: Cst, debug: bool, name: &str) {
    let mut compiler = Compiler::default();

    compiler.debug = debug;

    compiler.compile(instrs).unwrap();
    compiler.finish(name);
}
