use tokenise::{tokenize, tokenize_all};
mod codegen;
mod cst;

mod tokenise;
fn main() {
    show_output();
}

fn show_output() {
    let inp = r#"
    Actor hello {
        State hello;
        Initialiser {
            if 2 {
                return 2;
            };
            return 2;
        }
        Update (message) {
            if 2 {
                return 2;
            } else {
                return 5;
            };
        }
    }
    "#
    .chars()
    .collect::<Vec<char>>();
    let tokenised = tokenize_all(inp.as_slice()).unwrap();
    //println!("{tokenised:?}");
    let tree = cst::parse(&tokenised);
    println!("{tree:?}");

    //let mut x = codegen::Context::new();
    //x.test();
}
