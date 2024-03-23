#[derive(PartialEq, Debug, Clone, Hash, Eq)]
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
    Bottom,
    Forall(String, Box<Wff>),
    Exists(String, Box<Wff>),
    Atomic(String),             // a nullary predicate (proposition)
    PredApp(String, Vec<Term>), // n-ary predicate application (n >= 1)
    Equals(Term, Term),         // the equality predicate applied to two terms
}

#[derive(PartialEq, Debug)]
pub enum Justification {
    AndIntro(Vec<usize>),
    AndElim(usize),
    OrIntro(usize),
    OrElim(usize, Vec<(usize, usize)>),
    NotIntro((usize, usize)),
    NotElim(usize),
    BottomIntro(usize, usize),
    BottomElim(usize),
    ImpliesIntro((usize, usize)),
    ImpliesElim(usize, usize),
    EqualsIntro,
    EqualsElim(usize, usize),
    ForallIntro((usize, usize)),
    ForallElim(usize),
    ExistsIntro(usize),
    ExistsElim(usize, (usize, usize)),
    Reit(usize),
}

#[derive(PartialEq, Debug)]
pub struct ProofLine {
    pub line_num: Option<usize>, // None iff this line is a Fitch bar
    pub depth: usize,            // the number of vertical bars | on the left of this proof line
    pub is_premise: bool,        // true if either a main proof premise or subproof premise
    pub is_fitch_bar_line: bool,
    pub sentence: Option<Wff>, // None iff this line is a Fitch bar
    pub justification: Option<Justification>,
    pub constant_between_square_brackets: Option<Term>,
}

pub enum ProofResult {
    Correct,
    FatalError(String),
    Error(Vec<String>),
}
