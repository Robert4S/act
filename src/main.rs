use clap::Parser;
use cranegen::Compiler;
use std::{
    collections::{HashMap, HashSet},
    env, fs,
    path::PathBuf,
    process::Command,
    str::FromStr,
};
mod compiler;
use compiler::{
    cranegen,
    frontend::{
        cst::{self},
        tokenise,
        typecheck::TypeChecker,
    },
};

use cst::Cst;
use tokenise::tokenize_all;

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
    let mut tree = Cst {
        actors: Vec::new(),
        aliases: HashMap::new(),
        declarations: HashSet::new(),
    };
    cst::parse(&tokenised, &mut tree)
        .map_err(|e| format!("Error parsing: {e:?}, cst was: \n {tree:?}"))?;

    ["Unit", "Bool", "Int", "Float", "String"]
        .into_iter()
        .map(str::to_string)
        .for_each(|name| {
            tree.declarations.insert(name);
        });

    let _ = TypeChecker::validate_prog(tree.clone())
        .map_err(|e| format!("Error during validation: {e:?}"))?;

    gen_cranelift(tree, args.debug, &format!("{stem}.o"))?;

    let home = env::var("HOME").unwrap();

    Command::new("gcc")
        .arg("-o")
        .arg(stem.to_string())
        .arg(&format!("./{stem}.o"))
        .arg(format!("{home}/.local/lib/libact.a"))
        .arg("-lm")
        .status()
        .map_err(|_| "It seems you do not have GCC installed".to_string())
        .map(|_| ())?;

    let _ = fs::remove_dir_all("act_bin");

    fs::create_dir("act_bin").map_err(|e| e.to_string())?;
    fs::rename(format!("{stem}.o"), format!("./act_bin/{stem}.o")).map_err(|e| e.to_string())?;
    fs::rename(format!("{stem}"), format!("./act_bin/{stem}")).map_err(|e| e.to_string())
}

fn gen_cranelift(cst: Cst, debug: bool, name: &str) -> Result<(), String> {
    let mut compiler = Compiler::default();

    compiler.debug = debug;

    compiler
        .compile(cst)
        .map_err(|e| format!("Code generation error: {}", e.to_string()))?;
    compiler.finish(name);
    Ok(())
}
