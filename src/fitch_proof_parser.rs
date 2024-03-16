#[path = "data.rs"]
mod data;
use data::*;

pub fn parse_fitch_proof(proof: &str) -> Option<Proof> {
    let lines: Vec<&str> = proof.lines().filter(|s| !s.is_empty()).collect();
    todo!();
}

/* ----------------- PRIVATE -------------------*/

// This is the grammar of a Fitch proof:
//
// <FitchProof> is several <FitchProofLine>s separated by newline
// <FitchProofLine> ::= <num> '|' { '|' } <E1> [ <Justification> ]
//
// <E1> is a full logical expression as parsed by the function parse_logical_expression_string();
// the grammar for <E1> is defined in logic_expr.parser.rs.
//
// <num> is a non-negative decminal integer
//
// <Justification> ::=
//                      | Reit : <num>
//                      | (And | Or | Implies | Not | Forall | Exists) (Intro | Elim) :
