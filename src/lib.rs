use parser::parse_fitch_proof;
use wasm_bindgen::prelude::*;
mod checker;
mod data;
mod parser;
use crate::data::ProofResult;

#[wasm_bindgen]
pub fn check_proof(proof: &str) -> String {
    match parse_fitch_proof(proof) {
        Ok(proof_lines) => {
            let res = checker::check_proof(proof_lines);
            match res {
                ProofResult::Correct => "The proof is correct!".to_string(),
                ProofResult::Error(errs) => errs.join("\n\n"),
                ProofResult::FatalError(err) => format!("Fatal error: {err}"),
            }
        }
        Err(err) => format!("Fatal error: {err}"),
    }
}

fn _main() {
    /*println!(
        "{:?}",
        logic_expr_parser::parse_logical_expression_string(
            //"∀ x∀ x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)"
            "∀ x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))"
        )
    );
    println!("{:?}", logic_expr_parser::parse_fitch_proof("42 || A  Reit : 42"));*/
    /*println!(
            "{:?}",
            parser::parse_fitch_proof(
                // This proof is from one of the logic worksheets I made (available to all students)
                "
    1  | ∀x∀y(Likes(x,y)→Likes(y,x))
    2  | ∃x∀y Likes(x,y)
       | ----
    3  | | [c] ∀y Likes(c,y)
    4  | | | [d]
       | | | -
    5  | | | ∀y(Likes(c,y)→Likes(y,c)) ∀ Elim: 1
    6  | | | Likes(c,d)→Likes(d,c)     ∀ Elim: 5
    7  | | | Likes(c,d)                ∀ Elim: 3
    8  | | | Likes(d,c)                → Elim: 6, 7
    9  | | | ∃y Likes(d,y)             ∃ Intro: 8
    10 | | ∀x∃y Likes(d,y)             ∀ Intro: 4-9
    11 | ∀x∃y Likes(d,y)               ∃ Elim: 2, 3-10
    "
            )
        );*/
    /*checker::check_proof(
                // This proof is from one of the logic worksheets I made (available to all students)
                "
    1  | ∀x∀y(Likes(x,y)→Likes(y,x))
    2  | ∃x∀y Likes(x,y)
       | ----
    3  | | [c] ∀y Likes(c,y)
    4  | | | [d]
       | | | -
    5  | | | ∀y(Likes(c,y)→Likes(y,c)) ∀ Elim: 1
    6  | | | Likes(c,d)→Likes(d,c)     ∀ Elim: 5
    7  | | | Likes(c,d)                ∀ Elim: 3
    8  | | | Likes(d,c)                → Elim: 6, 7
    9  | | | ∃y Likes(d,y)             ∃ Intro: 8
    10 | | ∀x∃y Likes(d,y)             ∀ Intro: 4-9
    11 | ∀x∃y Likes(d,y)               ∃ Elim: 2, 3-10
    "
            );*/
    check_proof(
        "
1  | C
2  | B
   | ----
2  | A  ∧B   ∧ Intro:1,2
",
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn sometest() {
        println!("hi");
        println!("{}",check_proof(
            "
1 | A → C
2 | B → C
  | -----
3 | | A ∨ B
  | |----
4 | | | A
  | | |---
5 | | | C     →Elim:1,4
  | |
6 | | | B
  | | |---
7 | | | C     →Elim:2,6
8 | | C
9 | (A ∨ B) → C →Intro:3-8
 
"
        ));
        crate::check_proof("\n");
    }
}
