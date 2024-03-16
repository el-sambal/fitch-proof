#[derive(PartialEq, Debug)]
pub enum Term {
    Atomic(String),             // a variable or a constant
    FuncApp(String, Vec<Term>), // function application
}

#[derive(PartialEq, Debug)]
// well-formed formula (well, you have to hope it's well-formed...)
pub enum Wff {
    And(Vec<Wff>),
    Or(Vec<Wff>),
    Implies(Box<Wff>, Box<Wff>),
    Not(Box<Wff>),
    Forall(String, Box<Wff>),
    Exists(String, Box<Wff>),
    Atomic(String),             // a nullary predicate (proposition)
    PredApp(String, Vec<Term>), // n-ary predicate application (n >= 1)
    Equals(Term, Term),         // the equality function applied to two terms
}

#[derive(PartialEq, Debug)]
pub enum Justification {
    AndIntro(Vec<usize>),
    AndElim(usize),
    OrIntro(usize),
    OrElim(usize, Vec<(usize, usize)>),
    NotIntro((usize, usize)),
    NotElim(usize),
    ImpliesIntro((usize, usize)),
    ImpliesElim(usize, usize),
    ForallIntro((usize, usize)),
    ForallElim(usize),
    ExistsIntro(usize),
    ExistsElim(usize, (usize, usize)),
    Reit(usize),
}

#[derive(PartialEq, Debug)]
pub struct ProofLine {
    pub line_num:usize,
    pub depth: usize,     // the number of vertical bars | on the left of this proof line
    pub is_premise: bool, // either a main proof premise or subproof premise
    pub sentence: Wff,
    pub justification: Justification,
}

pub type Proof = Vec<ProofLine>;
