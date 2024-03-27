use std::collections::HashSet;

use parser::parse_fitch_proof;
use wasm_bindgen::prelude::*;
mod checker;
mod data;
mod parser;
use crate::data::ProofResult;

macro_rules! default_variable_names {
    () => {
        HashSet::from(["x".to_string(), "y".to_string(), "z".to_string(), "u".to_string()])
    };
}

#[wasm_bindgen]
pub fn check_proof(proof: &str) -> String {
    check_proof_with_defined_set_variable_names(proof, default_variable_names!())
}

pub fn check_proof_with_defined_set_variable_names(
    proof: &str,
    allowed_variable_names: HashSet<String>,
) -> String {
    let res = check_proof_to_proofresult(proof, allowed_variable_names);
    match res {
        ProofResult::Correct => "The proof is correct!".to_string(),
        ProofResult::Error(errs) => errs.join("\n\n"),
        ProofResult::FatalError(err) => format!("Fatal error: {err}"),
    }
}

pub fn check_proof_to_proofresult(
    proof: &str,
    allowed_variable_names: HashSet<String>,
) -> ProofResult {
    match parse_fitch_proof(proof) {
        Ok(proof_lines) => checker::check_proof(proof_lines, allowed_variable_names),
        Err(err) => ProofResult::FatalError(err),
    }
}

pub fn proof_is_correct(proof: &str) -> bool {
    matches!(check_proof_to_proofresult(proof, default_variable_names!()), ProofResult::Correct)
}
