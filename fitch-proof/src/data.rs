/// a [ProofLine] corresponds *directly* to one line in the user's inputted proof.
///
/// If a user types in a proof (which is a string), then this proof is split into lines (which are
/// also strings), and each of these lines correspond directly to one [ProofLine].
///
/// There are exactly 6 possible types of lines that the user can make:
/// 1. an empty line, consisting of only a positive number of vertical bars
/// 2. a Fitch bar line, which consists of a positive number of vertical bars followed by a
///    positive number of minuses.
/// 3. a premise that only introduces a boxed constant, without a logical sentence
/// 4. a premise that contains only a logical sentence, no boxed constant
/// 5. a premise that contains both a boxed constant introduction and a logical sentence
/// 6. an inference: a line that contains a sentence and justification
///
/// Each line of the user's input must correspond to exactly one of the above types. If the user
/// writes garbage, then it is not possible to convert it into [ProofLine]s and a fatal error will
/// be given to the user.
#[derive(PartialEq, Debug)]
pub struct ProofLine {
    /// The line number of the proof line. This is *not* the index at which the current line
    /// occured in the input string that the user gave, but it is the line number inside a Fitch
    /// proof that the user wrote themselves. For example, for a line like this:
    ///
    /// `42 | | | | P(a,b,c,d)  =Elim:137,108`
    ///
    /// this field in the struct would be `Some(42)`. This field must be [None] if and only if the
    /// corresponding line was an empty line or a Fitch bar line. In all other cases, the line
    /// number must be [Some(_)].
    pub line_num: Option<usize>,
    /// The number of vertical bars on the left side. This indicates in how many nested subproofs
    /// this proof line is.
    ///
    /// For example, this line would have a `depth` of `4`, since there are four vertical bars.
    ///
    /// `42 | | | | P(a,b,c,d)  =Elim:137,108`
    pub depth: usize,
    // This field is `true` if and only if the corresponding proof line is a Fitch bar line.
    pub is_fitch_bar_line: bool,
    // The logical sentence ([Wff]) that this proof line contains.
    //
    // This field must be [None] if this proof line does not contain a sentence, which is
    // if you have a premise that only introduces a boxed constant without sentence, or if
    // you have an empty line or a Fitch bar line.
    pub sentence: Option<Wff>,
    /// If the current proof line has a justification, it is stored in this field.
    ///
    /// If the current proof line has no justification, then this field should be [None]. This can
    /// be the case for example for a premise, empty line, or Fitch bar line. It could also be that
    /// the user intended this to be an inference, but simply did not write the justification yet.
    pub justification: Option<Justification>,
    /// If the current proof line is a premise that introduces a constant in a box, then this field
    /// contains it.
    pub constant_between_square_brackets: Option<Term>,
}

/// This a logical term. A term can be either a constant, a variable, or a function application
/// (which is a function applied to a positive number of terms).
#[derive(PartialEq, Debug, Clone, Hash, Eq)]
pub enum Term {
    /// A variable or constant.
    Atomic(String),
    // Function application
    FuncApp(String, Vec<Term>),
}

#[derive(PartialEq, Debug, Clone)]
/// A logical sentence. "Wff" stands for "well-formed formula", but this is a slightly incorrect
/// name, since for example, a logical sentence that has predicate ariy mismatches is still
/// expressable in this [Wff]. A [Wff] is a core element of a proof. For example, each proof line
/// that has a line number, will contain a [Wff] (unless it is a line which only introduces a boxed
/// constant).
pub enum Wff {
    /// Conjunction.
    And(Vec<Wff>),
    /// Disjunction.
    Or(Vec<Wff>),
    /// Implication.
    Implies(Box<Wff>, Box<Wff>),
    /// Biconditional.
    Bicond(Box<Wff>, Box<Wff>),
    /// Negation.
    Not(Box<Wff>),
    /// Bottom / contradiction.
    Bottom,
    /// Universal quantification.
    ///
    /// The associated [String] denotes the name of the variable that is quantified over, and the
    /// associated [Wff] is the rest of the sentence.
    Forall(String, Box<Wff>),
    /// Existential quantification.
    ///
    /// The associated [String] denotes the name of the variable that is quantified over, and the
    /// associated [Wff] is the rest of the sentence.
    Exists(String, Box<Wff>),
    /// This is a nullary predicate, for example "P".
    Atomic(String),
    /// This is n-ary predicate application, for n >= 1.
    ///
    /// For example, if you have the predicate application `P(x,y,f(a))`, then the associated [String]
    /// would be "P" and the associated vector of [Term]s would correspond to `x`, `y` and `f(a)`,
    /// respectively.
    PredApp(String, Vec<Term>),
    /// The equality predicate, applied to two [Term]s.
    Equals(Term, Term),
}

/// This enum represents the justification rules for an inference. The associated [usize]s denote
/// the line numbers being represented.
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
    BicondIntro((usize, usize), (usize, usize)),
    BicondElim(usize, usize),
    EqualsIntro,
    EqualsElim(usize, usize),
    ForallIntro((usize, usize)),
    ForallElim(usize),
    ExistsIntro(usize),
    ExistsElim(usize, (usize, usize)),
    Reit(usize),
}

pub enum ProofResult {
    /// No mistakes; proof is correct.
    Correct,
    /// An 'error' is a mistake that makes the proof wrong, but still allows
    /// the checker to go on and find other mistakes. This [ProofResult::Error]
    /// variant denotes the list of errors that was obtained during analysis.
    Error(Vec<String>),
    /// A mistake that is so severe that the checker cannot continue its analysis.
    /// When a fatal error occurs, this fatal error will be returned to the user,
    /// with no other error messages along it.
    ///
    /// Note that when the user checks some proof that should match to some proof template,
    /// a [ProofResult::FatalError] will be returned if the proof does
    /// not match the template.
    FatalError(String),
}
