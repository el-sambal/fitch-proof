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
fn test_exists_no_boxed_variable() {
    let proof = "
1 | ∃x P(x)
  | --
2 | | [z] P(z)
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
#[test]
fn test_multiple_exists_1() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
  | ------
3 | | [a] ∃y P(a,y)
  | | --
4 | | | [b] P(a,b)
  | | | --
5 | | | ∃z P(a,z)         ∃Intro:4
6 | | ∃z P(a,z)         ∃Elim:3,4-5
7 | | ∃u∃z P(u,z)       ∃Intro:6
8 |  ∃u∃z P(u,z)          ∃Elim:1,3-7
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_2() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
  | ------
3 | | [a] ∃y P(a,y)
  | | --
4 | | | [b] P(a,b)
  | | | --
5 | | | ∃z P(a,z)         ∃Intro:4
6 | | ∃z P(a,z)         ∃Elim:3,4-5
7 | | ∃u∃z P(u,z)       ∃Intro:6
8 |  ∃u∃z P(u,z)          ∃Elim:1,3-7
9 | a=a                =Intro
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_3() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
  | ------
3 | | [a] ∃y P(a,y)
  | | --
4 | | | [b] P(a,b)
  | | | --
5 | | | ∃z P(a,z)         ∃Intro:4
6 | | ∃z P(a,z)         ∃Elim:3,4-5
7 | | ∃u∃z P(u,z)       ∃Intro:6
8 |  ∃u∃z P(u,z)          ∃Elim:1,3-7
9 | b=b                =Intro
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_4() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
  | ------
3 | | [a] ∃y P(a,y)
  | | --
4 | | | [b] P(a,b)
  | | | --
5 | | | ∃z P(a,z)         ∃Intro:4
6 | | ∃z P(a,z)         ∃Elim:3,4-5
7 | | ∃u∃z P(u,z)       ∃Intro:6
8 |  ∃u∃z P(u,z)          ∃Elim:1,3-7
9 | a=b                ⊥Elim:2
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_5() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
  | ------
3 | | [a] ∃y P(a,y)
  | | --
4 | | | [b] P(a,b)
  | | | --
5 | | | ∃z P(a,z)         ∃Intro:4
6 | | ∃z P(a,z)         ∃Elim:3,4-5
7 | | ∃u∃z P(u,z)       ∃Intro:6
8 | a=a                  =Intro
9 |  ∃u∃z P(u,z)          ∃Elim:1,3-7
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_6() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
  | ------
3 | | [a] ∃y P(a,y)
  | | --
4 | | | [b] P(a,b)
  | | | --
5 | | | ∃z P(a,z)         ∃Intro:4
6 | | a=a              =Intro
7 | | ∃z P(a,z)         ∃Elim:3,4-5
8 | | ∃u∃z P(u,z)       ∃Intro:7
9 |  ∃u∃z P(u,z)          ∃Elim:1,3-8
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_7() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
  | ------
3 | | [a] ∃y P(a,y)
  | | --
4 | | | [b] P(a,b)
  | | | --
5 | | | ∃z P(a,z)         ∃Intro:4
6 | | b=b              =Intro
7 | | ∃z P(a,z)         ∃Elim:3,4-5
8 | | ∃u∃z P(u,z)       ∃Intro:7
9 |  ∃u∃z P(u,z)          ∃Elim:1,3-8
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_8() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
  | ------
3 | | [a] ∃y P(a,y)
  | | --
4 | | | [b] P(a,b)
  | | | --
5 | | | a=a         =Intro
6 | | | ∃z P(a,z)         ∃Intro:4
7 | | ∃z P(a,z)         ∃Elim:3,4-6
8 | | ∃u∃z P(u,z)       ∃Intro:7
9 |  ∃u∃z P(u,z)          ∃Elim:1,3-8
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_9() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
  | ------
3 | | [a] ∃y P(a,y)
  | | --
4 | | | [b] P(a,b)
  | | | --
5 | | | b=b         =Intro
6 | | | ∃z P(a,z)         ∃Intro:4
7 | | ∃z P(a,z)         ∃Elim:3,4-6
8 | | ∃u∃z P(u,z)       ∃Intro:7
9 |  ∃u∃z P(u,z)          ∃Elim:1,3-8
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_10() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
  | ------
3 | | [a] ∃y P(a,y)
  | | --
4 | | a=a                =Intro
5 | | | [b] P(a,b)
  | | | --
6 | | | ∃z P(a,z)         ∃Intro:5
7 | | ∃z P(a,z)         ∃Elim:3,5-6
8 | | ∃u∃z P(u,z)       ∃Intro:7
9 |  ∃u∃z P(u,z)          ∃Elim:1,3-8
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_11() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
  | ------
3 | | [a] ∃y P(a,y)
  | | --
4 | | b=b                =Intro
5 | | | [b] P(a,b)
  | | | --
6 | | | ∃z P(a,z)         ∃Intro:5
7 | | ∃z P(a,z)         ∃Elim:3,5-6
8 | | ∃u∃z P(u,z)       ∃Intro:7
9 |  ∃u∃z P(u,z)          ∃Elim:1,3-8
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_12() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
3 | a=a
  | ------
4 | | [a] ∃y P(a,y)
  | | --
5 | | | [b] P(a,b)
  | | | --
6 | | | ∃z P(a,z)         ∃Intro:5
7 | | ∃z P(a,z)         ∃Elim:4,5-6
8 | | ∃u∃z P(u,z)       ∃Intro:7
9 |  ∃u∃z P(u,z)          ∃Elim:1,4-8
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_multiple_exists_13() {
    let proof = "
1 | ∃x∃y P(x,y)
2 | ⊥
3 | b=b
  | ------
4 | | [a] ∃y P(a,y)
  | | --
5 | | | [b] P(a,b)
  | | | --
6 | | | ∃z P(a,z)         ∃Intro:5
7 | | ∃z P(a,z)         ∃Elim:4,5-6
8 | | ∃u∃z P(u,z)       ∃Intro:7
9 |  ∃u∃z P(u,z)          ∃Elim:1,4-8
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_forall_1() {
    let proof = "
1 | ∀x P(x)
2 | ⊥
  | ---
3 | | [d]
  | | --
4 | | P(d)     ∀Elim:1
5 | ∀x P(x)    ∀Intro:3-4
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_forall_2() {
    let proof = "
1 | ∀x P(x)
2 | ⊥
  | ---
3 | | [d]
  | | --
4 | | P(d)     ∀Elim:1
5 | ∀y P(y)    ∀Intro:3-4
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_forall_3() {
    let proof = "
1 | ∀x P(x)
2 | ⊥
  | ---
3 | | [d]
  | | --
4 | | P(d)     ∀Elim:1
5 | ∀y P(d)    ∀Intro:3-4
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_forall_4() {
    let proof = "
1 | ∀x P(x)
2 | ⊥
  | ---
3 | | [d]
  | | --
4 | | P(d)     ∀Elim:1
5 | ∀d P(y)    ∀Intro:3-4
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_forall_5() {
    let proof = "
1 | ∀x P(x)
2 | ⊥
  | ---
3 | | [d]
  | | --
4 | | P(d)     ∀Elim:1
5 | ∀d P(d)    ∀Intro:3-4
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_forall_6() {
    let proof = "
1 | ∀x P(x)
2 | ⊥
  | ---
3 | | [d]
  | | --
4 | | d=d      =Intro
5 | ∀x (x=x)    ∀Intro:3-4
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_forall_7() {
    let proof = "
1 | ∀x P(x)
2 | ⊥
  | ---
3 | | [d]
  | | --
4 | | d=d      =Intro
5 | ∀x (d=x)    ∀Intro:3-4
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_forall_8() {
    let proof = "
1 | ∀x P(x)
2 | ⊥
  | ---
3 | | [c]
  | | --
4 | | d=d      =Intro
5 | ∀x (x=x)    ∀Intro:3-4
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_forall_9() {
    let proof = "
1 | ∀x P(x)
2 | ⊥
  | ---
3 | | [d] d=d
  | | --
4 | | d=d      =Intro
5 | ∀x (x=x)    ∀Intro:3-4
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_intro_zero_or_more_1() {
    let proof = "
1 | S(c,c,c)
  | ----
2 | ∃u S(c,c,c)   ∃Intro:1
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_intro_zero_or_more_2() {
    let proof = "
1 | S(c,c,c)
  | ----
2 | ∃u S(u,c,c)   ∃Intro:1
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_intro_zero_or_more_3() {
    let proof = "
1 | S(c,c,c)
  | ----
2 | ∃u S(u,c,u)   ∃Intro:1
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_intro_zero_or_more_4() {
    let proof = "
1 | S(c,c,c)
  | ----
2 | ∃u S(u,u,u)   ∃Intro:1
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_intro_zero_or_more_5() {
    let proof = "
1 | S(c,c,u)
  | ----
2 | ∃u S(c,c,c)   ∃Intro:1
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_intro_zero_or_more_6() {
    let proof = "
1 | S(c,c,c)
  | ----
2 | ∃x S(c,c,c)   ∃Intro:1
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_intro_zero_or_more_7() {
    let proof = "
1 | S(c,c,c)
  | ----
2 | ∃a S(c,c,c)   ∃Intro:1
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_exists_intro_zero_or_more_8() {
    let proof = "
1 | S(c,c,c)
  | ----
2 | ∃c S(c,c,c)   ∃Intro:1
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_bicond_elim_1() {
    let proof = "
1 | A↔B
2 | B
3 | A
  | --
4 | A     ↔ Elim:1,2
5 | B     ↔ Elim:1,4
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_bicond_elim_2() {
    let proof = "
1 | A↔B
2 | B
3 | A
  | --
4 | A     ↔ Elim:1,3
5 | B     ↔ Elim:1,4
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_bicond_elim_3() {
    let proof = "
1 | A↔B
2 | B
3 | A
  | --
4 | A     ↔ Elim:2,1
5 | B     ↔ Elim:1,4
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_bicond_elim_4() {
    let proof = "
1 | A↔B
2 | B
3 | A
  | --
4 | A     ↔ Elim:1,5
5 | B     ↔ Elim:1,4
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_bicond_intro_1() {
    let proof = "
1 | A→B
2 | B→A
  | ---
3 | | A
  | | ---
4 | | B     →Elim: 1,3
  |
5 | | B
  | | ---
6 | | A     →Elim: 2,5
7 | A↔B     ↔Intro:3-4,5-6
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_bicond_intro_2() {
    let proof = "
1 | A→B
2 | B→A
  | ---
3 | | A
  | | ---
4 | | B     →Elim: 1,3
  |
5 | | B
  | | ---
6 | | A     →Elim: 2,5
7 | A↔B     ↔Intro:5-6,3-4
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_bicond_intro_3() {
    let proof = "
1 | A→B
2 | B→A
  | ---
3 | | A
  | | ---
4 | | B     →Elim: 1,3
  |
5 | | B
  | | ---
6 | | A     →Elim: 2,5
7 | B↔A     ↔Intro:3-4,5-6
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_bicond_intro_4() {
    let proof = "
1 | A→B
2 | B→A
  | ---
3 | | A
  | | ---
4 | | B     →Elim: 1,3
  |
5 | | B
  | | ---
6 | | A     →Elim: 2,5
7 | B↔A     ↔Intro:5-6,3-4
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_bicond_intro_5() {
    let proof = "
1 | A→B
2 | B→A
  | ---
3 | | [a] A
  | | ---
4 | | B     →Elim: 1,3
  |
5 | | B
  | | ---
6 | | A     →Elim: 2,5
7 | B↔A     ↔Intro:5-6,3-4
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_implies_intro_1() {
    let proof = "
1 | A→B
  | ---
2 | | A
  | | ---
3 | | B      →Elim:1,2
4 | A→B      →Intro:2-3
";

    assert!(fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_implies_intro_2() {
    let proof = "
1 | A→B
  | ---
2 | | [a] A
  | | ---
3 | | B      →Elim:1,2
4 | A→B      →Intro:2-3
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_implies_intro_3() {
    let proof = "
1 | A→B
  | ---
2 | | [A] A
  | | ---
3 | | B      →Elim:1,2
4 | A→B      →Intro:2-3
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
#[test]
fn test_implies_intro_4() {
    let proof = "
1 | A→B
  | ---
2 | | A
  | | ---
3 | | B      →Elim:2,1
4 | A→B      →Intro:2-3
";

    assert!(!fitch_proof::proof_is_correct(proof));
}
