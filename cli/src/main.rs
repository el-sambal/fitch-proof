extern crate fitch_proof;

const DEFAULT_ALLOWED_VARIABLE_NAMES: &str = "x,y,z,u,v,w";

/// Print an error message that file could not be found and exit.
fn fail_open_file(filename: &str) -> ! {
    println!(
        "Oops, it seems like the file {} could not be opened. Are you sure it exists? Aborting.",
        filename
    );
    std::process::exit(1)
}

/// Finds the name of the .txt file in the current directory. On Themis, this is the proof that the
/// student uploaded. If there are multiple .txt files, abort. If there is no .txt file, abort.
/// Otherwise, returns the name of the .txt file that was found.
fn find_txt_file() -> String {
    let mut already_found_txt = false;
    let paths = std::fs::read_dir("./").unwrap(); // all files
    let mut filename = "".to_string(); // whatever file is being processed (not necessary .txt)
    let mut txt_filename = "".to_string(); // what we're going to return

    for path in paths {
        let old_txt_filename = txt_filename.clone();
        filename = path.unwrap().path().display().to_string();

        if filename.ends_with(".txt") {
            if already_found_txt {
                println!(
                    "It seems you uploaded several .txt files.
                    The found files are {} and {}. Aborting.",
                    old_txt_filename, filename
                );
                std::process::exit(1);
            }
            txt_filename.clone_from(&filename);
            already_found_txt = true;
        }
    }

    if already_found_txt {
        filename
    } else {
        println!(
            "Could not find a .txt file in this directory.
            Did you upload a .txt file? Aborting."
        );
        std::process::exit(1);
    }
}

/// The *proof* itself (what the student wrote) should be in some .txt file in the same directory
/// as the executable. The executable will detect this .txt file itself.
///
/// The *proof template* should be given via `stdin`.
///
/// Currently, there is NO SUPPORT for a custom set of allowed variable names over the command
/// line (it is only in the web GUI).
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

    let result: String = fitch_proof::check_proof_with_template(&proof, template, &variables);
    println!("{}", result);
}
