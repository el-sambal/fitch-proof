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
1 | A → (a=b)
2 | B → (f(g(a),=b)
3 | ¬¬(a=b) → ¬(P∨¬P)
4 | ¬(b=c)
  | -----
5 | | A ∨ B
  | |----
6 | | | A
  | | |---
7 | | | a=b               →Elim:1,6
8 | | | | ¬(a=b)        
  | | | | -----
9 | | | | ⊥               ⊥Intro: 7,8
10| | | ¬¬(a=b)           ¬Intro: 8-9
11| | | ¬(P∨¬P)           →Elim: 3, 10
12| | | | P
  | | | |---
13| | | | P∨¬P            ∨Intro: 12
14| | | | ⊥               ⊥Intro:13,11
15| | | ¬P                ¬Intro:12-14
16| | | P∨¬P              ∨Intro: 15
17| | |⊥                  ⊥Intro: 16,11
  | |
18| | | B
  | | | ---
19| | | c=b               →Elim:2,18
20| | | c=c               =Intro
21| | | b=c               =Elim: 20,19
22| | | ⊥                 ⊥Intro: 21,4
23| | ⊥                   ∨Elim:  5,6-17, 18-22
24| ¬(A∨ B)               ¬Intro: 5-23
 
"
        ));
        crate::check_proof("\n");
    }
}
