#[test]
fn test_closed_term_substitution_1() {
    let proof = "
1 | ∀x ∃y P(x,y)
  | ----
2 | ∃y P(f(a),y)     ∀Elim:1
3 | ∃z ∃y P(f(a),z)  ∃Intro:2
";
    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_closed_term_substitution_2() {
    let proof = "
1 | ∀x ∃y P(x,y)
  | ----
2 | ∃y P(f(a),y)     ∀Elim:1
3 | ∃z ∃y P(z,y)  ∃Intro:2
";
    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_closed_term_substitution_3() {
    let proof = "
1 | ∀x ∃y P(x,y)
  | ----
2 | ∃y P(f(a),y)     ∀Elim:1
3 | ∃z ∃y P(f(z),y)  ∃Intro:2
";
    assert!(fitch_proof::proof_is_correct(proof));
}
