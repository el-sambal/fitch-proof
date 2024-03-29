use parser::parse_allowed_variable_names;
use parser::parse_fitch_proof;
use wasm_bindgen::prelude::*;
mod checker;
mod data;
mod formatter;
mod parser;
use crate::data::ProofResult;

macro_rules! default_variable_names {
    () => {
        "x,y,z,u,v,w"
    };
}

#[wasm_bindgen]
pub fn check_proof(proof: &str, allowed_variable_names: &str) -> String {
    let res = check_proof_to_proofresult(proof, allowed_variable_names);
    match res {
        ProofResult::Correct => "The proof is correct!".to_string(),
        ProofResult::Error(errs) => errs.join("\n\n"),
        ProofResult::FatalError(err) => format!("Fatal error: {err}"),
    }
}

pub fn check_proof_to_proofresult(proof: &str, allowed_variable_names: &str) -> ProofResult {
    match (parse_fitch_proof(proof), parse_allowed_variable_names(allowed_variable_names)) {
        (Ok(proof_lines), Ok(variable_names)) => checker::check_proof(proof_lines, variable_names),
        (Err(err), _) | (_, Err(err)) => ProofResult::FatalError(err),
    }
}

pub fn proof_is_correct(proof: &str) -> bool {
    matches!(check_proof_to_proofresult(proof, default_variable_names!()), ProofResult::Correct)
}

#[wasm_bindgen]
pub fn format_proof(proof: &str) -> String {
    match parse_fitch_proof(proof) {
        Ok(lines) if !lines.is_empty() => formatter::format_proof(lines),
        _ => proof.to_owned(),
    }
}
