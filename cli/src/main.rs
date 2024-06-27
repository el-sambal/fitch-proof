extern crate fitch_proof;

const DEFAULT_ALLOWED_VARIABLE_NAMES: &str = "x,y,z,u,v,w";

fn fail_open_file(filename: &str) -> ! {
    println!(
        "Oops, it seems like the file {} could not be opened. Are you sure it exists?",
        filename
    );
    std::process::exit(1)
}

fn main() {
    let mut paths = std::fs::read_dir("./").unwrap();
    let proof_filename = paths.next().unwrap().unwrap().path().display().to_string();
    let Ok(proof) = std::fs::read_to_string(&proof_filename) else {
        fail_open_file(&proof_filename)
    };
    let template: Vec<String> = std::io::stdin()
        .lines()
        .map(|s| s.unwrap().trim().to_string())
        .collect();
    let variables = DEFAULT_ALLOWED_VARIABLE_NAMES.to_string();

    let result = fitch_proof::check_proof_with_template(&proof, template, &variables);
    println!("{}", result);
}
