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
#[test]
fn test_random_stuff() {
    let proof = "

1 | A → (a=b)
2 | B → (f(g(a),h(a,b))=b)
3 | ¬¬(a=b) → ¬(P∨¬P)
4 | ¬(b=f(g(a),h(a,b)))
  | -----
5 | | A ∨ B
  | |----
6 | | | A
  | | |---
7 | | | a=b                          →Elim:1,6
8 | | | | ¬(a=b)        
  | | | | -----
9 | | | | ⊥                           ⊥Intro: 7,8
10| | | ¬¬(a=b)                       ¬Intro: 8-9
11| | | ¬(P∨¬P)                       →Elim: 3, 10
12| | | | P
  | | | |---
13| | | | P∨¬P                        ∨Intro: 12
14| | | | ⊥                           ⊥Intro:13,11
15| | | ¬P                            ¬Intro:12-14
16| | | P∨¬P                           ∨Intro: 15
17| | |⊥                               ⊥Intro: 16,11
  | |
18| | | B
  | | | ---
19| | | f(g(a),h(a,b))=b               →Elim:2,18
20| | | f(g(a),h(a,b))=f(g(a),h(a,b))  =Intro
21| | | b=f(g(a),h(a,b))               =Elim: 20,19
22| | | ⊥                              ⊥Intro: 21,4
23| | ⊥                                ∨Elim:  5,6-17, 18-22
24| ¬(A∨ B)                           ¬Intro: 5-23";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_stuff() {
    let proof = "
1 | ∃x P(x)
  | --
2 | | [c] P(c)
  | | --
3 | | ∃y P(y)     ∃Intro: 2
4 | ∃y P(y)       ∃Elim: 1,2-3";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_conclusion_does_not_match() {
    let proof = "
1 | ∃x P(x)
  | --
2 | | [c] P(c)
  | | --
3 | | ∃y P(y)     ∃Intro: 2
4 | ∃z P(z)       ∃Elim: 1,2-3";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_no_boxed_const() {
    let proof = "
1 | ∃x P(x)
  | --
2 | | P(c)
  | | --
3 | | ∃y P(y)     ∃Intro: 2
4 | ∃y P(y)       ∃Elim: 1,2-3";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_more_exists_stuff() {
    let proof = "
1 | ∃x P(x)
  | --
2 | | [c] P(x)
  | | --
3 | | ∃y P(y)     ∃Intro: 2
4 | ∃y P(y)       ∃Elim: 1,2-3";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_stuff_wrong_constant_in_box() {
    let proof = "
1 | ∃x P(x)
  | --
2 | | [d] P(c)
  | | --
3 | | ∃y P(y)     ∃Intro: 2
4 | ∃y P(y)       ∃Elim: 1,2-3";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_boxed_constant_subproof() {
    let proof = "
1 | ∃x P(x)
  | --
2 | | [c] P(c)
  | | --
3 | | P(c)        Reit: 2
4 | P(c)       ∃Elim: 1,2-3";

    assert!(!fitch_proof::proof_is_correct(proof));
}
