let ex1 = `1 | A ∧ B
  |----
2 | B             ∧ Elim: 1
3 | A             ∧ Elim: 1
4 | B ∧ A         ∧ Intro: 2, 3`;

let ex2 = `1 | P(a) ∧ P(b)
2 | (a=c) ∨ (b=c)
  |----
3 | | a=c
  | |----
4 | | P(a)                ∧ Elim: 1
5 | | P(c)                = Elim: 4, 3
  |
6 | | b=c
  | |----
7 | | P(b)                ∧ Elim: 1
8 | | P(c)                = Elim: 7, 6
9 | P(c)                  ∨ Elim: 2, 3-5, 6-8`;
