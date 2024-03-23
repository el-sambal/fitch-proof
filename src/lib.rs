use parser::parse_fitch_proof;
use wasm_bindgen::prelude::*;
mod checker;
mod data;
mod parser;
use crate::data::ProofResult;

#[wasm_bindgen]
pub fn check_proof(proof: &str) -> String {
    let res = check_proof_to_proofresult(proof);
    match res {
        ProofResult::Correct => "The proof is correct!".to_string(),
        ProofResult::Error(errs) => errs.join("\n\n"),
        ProofResult::FatalError(err) => format!("Fatal error: {err}"),
    }
}

pub fn check_proof_to_proofresult(proof: &str) -> ProofResult {
    match parse_fitch_proof(proof) {
        Ok(proof_lines) => checker::check_proof(proof_lines),
        Err(err) => ProofResult::FatalError(err),
    }
}

pub fn proof_is_correct(proof: &str) -> bool {
    matches!(check_proof_to_proofresult(proof), ProofResult::Correct)
}
