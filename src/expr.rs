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
