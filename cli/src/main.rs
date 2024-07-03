extern crate fitch_proof;

const DEFAULT_ALLOWED_VARIABLE_NAMES: &str = "x,y,z,u,v,w";

fn fail_open_file(filename: &str) -> ! {
    println!(
        "Oops, it seems like the file {} could not be opened. Are you sure it exists?",
        filename
    );
    std::process::exit(1)
}

fn find_txt_file() -> String {
    let paths = std::fs::read_dir("./").unwrap();
    for path in paths {
        let filename = path.unwrap().path().display().to_string();
        if filename.ends_with(".txt") {
            return filename;
        }
    }
    "you-should-upload-a-dot-txt-file".to_string()
}

fn main() {
    let proof_file = find_txt_file();
    let Ok(proof) = std::fs::read_to_string(&proof_file) else {
        fail_open_file(&proof_file)
    };
    let template: Vec<String> = std::io::stdin()
        .lines()
        .map(|s| s.unwrap().trim().to_string())
        .collect();
    let variables = DEFAULT_ALLOWED_VARIABLE_NAMES.to_string();

    let result = fitch_proof::check_proof_with_template(&proof, template, &variables);
    println!("{}", result);
}
