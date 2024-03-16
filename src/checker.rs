use crate::data::*;
use crate::parser::parse_fitch_proof;

pub enum ProofResult {
    Correct,
    ParserError(String),
    LogicError(String),
}

pub fn check_proof(proof_str: &str) -> ProofResult {
    match parse_fitch_proof(proof_str) {
        Some(proof) => {
            for line in &proof {
                if let Err(err) = check_line(line, &proof) {
                    println!("{err}");
                } else {
                    println!("line verified!");
                }
            }
        }
        None => {
            return ProofResult::ParserError(
                "Something went wrong when parsing your proof!".to_string(),
            );
        }
    }
    todo!();
}

/* ------------------ PRIVATE ------------------ */

// get line, return proper error message if that line doesn't exist
// note that if the referenced line does exist, but does not contain a sentence, then this function
// will not catch that and still return an Ok(..) !
// this is intended, because sometimes you can refer to lines which contain only a boxed constant.
fn get_line(line: usize, proof: &Proof) -> Result<&ProofLine, String> {
    let li = proof.iter().find(|l| l.line_num == Some(line));
    if let Some(l) = li {
        Ok(l)
    } else {
        Err(format!("Error: in one of the justifications, line {line} is being referred to, but this line does not exist."))
    }
}

// same as get_line, but it returns instead the wff found at the requested line, and if this line
// does not contain a sentence then this function will return an Err().
fn get_wff_at_line(line: usize, proof: &Proof) -> Result<&Wff, String> {
    let li = proof.iter().find(|l| l.line_num == Some(line));
    if let Some(l) = li {
        if let Some(wff) = &l.sentence {
            Ok(wff)
        } else {
            Err(format!("In one of the justifications, line {line} is being referred to, but this line does not contain a sentence."))
        }
    } else {
        Err(format!("Error: in one of the justifications, line {line} is being referred to, but this line does not exist."))
    }
}

// checks the logical validity of a particular proof line
// i.e., checks if the proof rule in the given line has been applied correctly
fn check_line(line: &ProofLine, proof: &Proof) -> Result<(), String> {
    if line.is_premise || line.is_fitch_bar_line {
        return Ok(());
    }

    let mut curr_line_num: usize = usize::MAX;
    if let Some(line_num) = line.line_num {
        curr_line_num = line_num;
    }

    if let (Some(wff), Some(just)) = (&line.sentence, &line.justification) {
        match just {
            Justification::Reit(n) => {
                let ref_wff = get_wff_at_line(*n, proof)?;
                if ref_wff == wff {
                    return Ok(());
                } else {
                    return Err(format!("Error: in line {curr_line_num}, the proof rule Reit is used, but the sentence in this line is not the same as the sentence in the referenced line."));
                }
            }
            Justification::AndIntro(ns) => {
                if let Wff::And(conjs) = wff {
                    if ns.len() != conjs.len() {
                        return Err(format!("Error: in line {curr_line_num}, the conjuction introduction rule is used, but the number of conjuncts in that line is not equal to the number of referenced lines."));
                    }
                    for i in 0..ns.len()
                    {
                        if &conjs[i] != get_wff_at_line(ns[i],proof)? {
                            return Err(format!("In line {curr_line_num}, the conjunction introduction rule is used, but the {}\'th conjunct of that line is not the same as the sentence found in line {} (the {}\'th line referenced in the justification).",i+1,ns[i],i+1));
                        }
                    }
                    return Ok(())
                }
            }
            Justification::AndElim(n) => {}
            Justification::OrIntro(n) => {}
            Justification::OrElim(n, ns) => {}
            Justification::ImpliesIntro((n, m)) => {}
            Justification::ImpliesElim(n, m) => {}
            Justification::NotIntro((n, m)) => {}
            Justification::NotElim(n) => {}
            Justification::ForallIntro((n, m)) => {}
            Justification::ForallElim(n) => {}
            Justification::ExistsIntro(n) => {}
            Justification::ExistsElim(n, (i, j)) => {}
        }
    }

    Err(
        "Error: no idea what went wrong here. Please report this issue to the developer. Thanks!"
            .to_string(),
    )
}
