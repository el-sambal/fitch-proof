extern crate fitch_proof;

const DEFAULT_ALLOWED_VARIABLE_NAMES: &str = "x,y,z,u,v,w";

fn usage() -> ! {
    println!(
        "Hi, if you are a student and see this message on Themis,
please contact the course staff as soon as possible.
Likely, something is misconfigured on our side. Thanks!

--------------------------------------------

This is meant for whoever manages Themis:

Oops, something went wrong. This is how the program is supposed to be called:

      ./fitch-checker proof.txt < template.txt
OR
      ./fitch-checker proof.txt variables.txt < template.txt
 
Of course, <proof.txt> could be any filename, but we will call 
it proof.txt in the text below. The same applies for the other files.

Here, the file proof.txt should contain the full proof, as one
would write it in the web interface. The file template.txt should
contain only a number of logical sentences, namely (in order) the
premises and the final conclusion that the proof should lead to.
The idea is that the proof in proof.txt must match the template
in template.txt. The template should be given via stdin.

It is optional to provide the file variables.txt. If provided, this file
should contain the strings that should be seen as a variable. The file
should contain a single line that looks like this:

{}

The list of strings that should be seen as a variable should
be comma-separated. If the file variables.txt is not provided,
then a default value of \"{}\" is used.",
        DEFAULT_ALLOWED_VARIABLE_NAMES, DEFAULT_ALLOWED_VARIABLE_NAMES
    );

    std::process::exit(1);
}

fn fail_open_file(filename: &str) -> ! {
    println!(
        "Oops, it seems like the file {} could not be opened. Are you sure it exists?",
        filename
    );
    std::process::exit(1)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 && args.len() != 3 {
        usage()
    }
    let proof_filename = &args[1];
    let Ok(proof) = std::fs::read_to_string(proof_filename) else {
        fail_open_file(proof_filename)
    };
    let template: Vec<String> = std::io::stdin().lines().map(|s| s.unwrap().trim().to_string()).collect();
    let variables = if args.len() == 2 {
        DEFAULT_ALLOWED_VARIABLE_NAMES.to_string()
    } else {
        let variables_filename = &args[2];
        let Ok(variables) = std::fs::read_to_string(variables_filename) else {
            fail_open_file(variables_filename)
        };
        variables
    };

    let result = fitch_proof::check_proof_with_template(&proof,template, &variables);
    println!("{}", result);
}
