mod logic_expr_parser;
mod fitch_proof_parser;
fn main() {
    /*println!(
        "{:?}",
        logic_expr_parser::parse_logical_expression_string(
            //"∀ x∀ x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)"
            "∀ x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))"
        )
    );
    println!("{:?}", logic_expr_parser::parse_fitch_proof("42 || A  Reit : 42"));*/
    println!("{:?}", logic_expr_parser::parse_fitch_proof(
"
1 | A
2 | B
  | ----
3 | A ∧ B ∧Intro: 1,2
"
            ));
}
