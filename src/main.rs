mod fitch_proof_parser;
mod logic_expr_parser;
fn main() {
    /*println!(
        "{:?}",
        logic_expr_parser::parse_logical_expression_string(
            //"∀ x∀ x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)"
            "∀ x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))"
        )
    );
    println!("{:?}", logic_expr_parser::parse_fitch_proof("42 || A  Reit : 42"));*/
    println!(
        "{:?}",
        logic_expr_parser::parse_fitch_proof(
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
    );
}
