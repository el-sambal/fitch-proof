use crate::data::*;
use crate::parser::parse_fitch_proof;

pub enum ProofResult {
    Correct,
    FatalError(String),
    Error(Vec<String>),
}

// Name says it all.
pub fn check_proof(proof_str: &str) -> ProofResult {
    match parse_fitch_proof(proof_str) {
        Some(proof_lines) => match Proof::construct(proof_lines) {
            Err(err) => ProofResult::FatalError(err),
            Ok(proof) => proof.check(),
        },
        None => ProofResult::FatalError("Could not parse the proof!".to_string()),
    }
}

#[derive(Debug)]
enum ProofUnit {
    NumberedProofLineInference(usize),
    NumberedProofLinePremise(usize),
    FitchBarLine,
    SubproofOpen,
    SubproofClose,
}

// should be always constructed using the construct() method!!!!!
struct Proof {
    lines: Vec<ProofLine>,
    scope: Vec<(Vec<usize>, Vec<(usize, usize)>)>,
    units: Vec<ProofUnit>,
}
impl Proof {
    // Given a vector of ProofLines, this method constructs the proof. In case this method fails,
    // it means a fatal error will need to be given, because if this method already fails then the
    // proof is not even half-well-structured, and further analysis is impossible. After
    // construct()ing the proof, you should proof.check() it. The combination of these two things
    // allows you to assess the correctness of a proof.
    fn construct(proof_lines: Vec<ProofLine>) -> Result<Proof, String> {
        let units = Self::lines_to_units(&proof_lines)?;
        println!("{:?}", units);
        Self::is_half_well_structured(&units)?; // check if proof is HALF-well-structured
        let scope = Self::determine_scope(&units);

        println!("{:?}", scope);

        Ok(Proof {
            lines: proof_lines,
            scope,
            units,
        })
    }

    // given a Proof (which 'by definition' is half-well-structured,
    // otherwise its constructor would have failed), checks if it is fully correct.
    // Together with Proof::construct(), this is the method that you should run in
    // order to assess the validity of a proof.
    fn check(&self) -> ProofResult {
        let mut errors: Vec<String> = vec![];
        for line in &self.lines {
            if let Err(err) = self.check_line(line) {
                println!("{err}");
                errors.push(err.to_string());
            }
        }
        if let Err(err) = Self::is_fully_well_structured(&self.units) {
            errors.push(err.to_string());
        }

        if errors.is_empty() {
            println!("The proof is correct!");
            ProofResult::Correct
        } else {
            ProofResult::Error(errors)
        }
    }

    // checks if a proof is HALF-well-structured.
    // The reason that we make this distinction is because the algorithm does this:
    // -> (1) parse proof
    // -> (2) check that proof is HALF-well-structured
    // -> (3) check all lines of the proof
    // -> (4) check that proof is FULLY-well-structured
    // The point is that we want to give the user as helpful error messages as possible. We also
    // want to be able to give the user several meaningful messages at the same time. But if a
    // proof is not even half-well-structured, then it is not even possible to check all lines of
    // it, so a FATAL error will be given, in which case all the other analysis does not happen.
    // If the user has a HALF-but-not-FULLY-well-structured proof, then it is still possible to
    // perform the more detailed analysis in step 3, so we want that. In this case, the user will
    // get meaningful error messages from all proof lines that are wrong, and that is better than
    // only a fatal error when they for example just forget one justification.
    fn is_half_well_structured(units: &[ProofUnit]) -> Result<(), String> {
        Self::is_well_structured(units, true)
    }
    // checks if a proof is FULLY-well-structured
    fn is_fully_well_structured(units: &[ProofUnit]) -> Result<(), String> {
        Self::is_well_structured(units, false)
    }
    fn is_well_structured(units: &[ProofUnit], check_only_half: bool) -> Result<(), String> {
        // traverse the `ProofUnit`s to check validity of the proof
        // basically, for each "proof unit", we check that the units after that are allowed.
        match units[0] {
            ProofUnit::FitchBarLine => {}
            ProofUnit::NumberedProofLinePremise(_) => {}
            _ => {
                return Err("Error: proof should start with premises (or \
                Fitch bar, if there are no premises)."
                    .to_string())
            }
        }
        for i in 0..units.len() {
            match units[i] {
                ProofUnit::FitchBarLine => {
                    // in FULLY-well-structured proofs, a Fitch bar line may be only succeeded by:
                    //  - an inference
                    //  - a new subproof
                    //    and a proof MUST NOT end with a Fitch bar line.
                    //  ---------------------
                    // in HALF-well-structured proofs, a Fitch bar line may be succeeded by:
                    //  - an inference
                    //  - a premise (inference for which the user didn't write justification yet)
                    //  - a new subproof
                    //    and a proof MAY end with a Fitch bar line.
                    if i + 1 == units.len() {
                        if !check_only_half {
                            return Err("Error: the proof ends with a Fitch bar.".to_string());
                        }
                    } else {
                        match units[i + 1] {
                            ProofUnit::NumberedProofLineInference(_) => {}
                            ProofUnit::SubproofOpen => {}
                            ProofUnit::NumberedProofLinePremise(_) if check_only_half => {}
                            _ => {
                                return Err("Error: Fitch bars should be followed by \
                                           either a new subproof or an inference. \
                                           You might be missing a justification."
                                    .to_string());
                            }
                        }
                    }
                }
                ProofUnit::SubproofOpen => {
                    // in FULLY-well-structured proofs, after a subproof is opened, there must be:
                    //  - EXACTLY one numbered premise, FOLLOWED by a Fitch bar
                    //  ---------------------
                    // in HALF-well-structured proofs, the same requirements apply.
                    if i + 1 == units.len() || i + 2 == units.len() {
                        return Err("Error: this proof ends with an opened \
                                   subproof in a way that should not be."
                            .to_string());
                    }
                    match units[i + 1] {
                        ProofUnit::NumberedProofLinePremise(_) => {}
                        _ => {
                            return Err(
                                "Error: the first line on any new subproof should be a premise."
                                    .to_string(),
                            )
                        }
                    }
                    match units[i + 2] {
                        ProofUnit::FitchBarLine => {}
                        _ => {
                            return Err("Error: a subproof should have exactly one\
                                         premise, followed by a Fitch bar."
                                .to_string())
                        }
                    }
                }
                ProofUnit::SubproofClose => {
                    // in FULLY-well-structured proofs, after a closed subproof there should be either:
                    //  - an inference
                    //  - a new subproof
                    //    and a proof MUST NOT end directly after a closed subproof.
                    //  ---------------------
                    // in HALF-well-structured proofs, after a closed subproof there should be either:
                    //  - an inference
                    //  - a premise (inference for which user didn't write justification yet)
                    //  - a new subproof
                    //    and a proof MAY end directly after a closed subproof.
                    if i + 1 == units.len() {
                        if !check_only_half {
                            return Err("Error: the proof ends with the closing of a subproof.\
                                       The last line of the proof should always be top-level."
                                .to_string());
                        }
                    } else {
                        match units[i + 1] {
                            ProofUnit::NumberedProofLineInference(_) => {}
                            ProofUnit::SubproofOpen => {}
                            ProofUnit::NumberedProofLinePremise(_) if check_only_half => {}
                            _ => {
                                return Err("Error: after closing a subproof, either you \
                                     should open a new subproof or there should be \
                                     an inference. Maybe you are missing some justification."
                                    .to_string())
                            }
                        }
                    }
                }
                ProofUnit::NumberedProofLineInference(_) => {
                    // in FULLY-well-structured proofs, after an inference there should be either:
                    //  - the end of the subproof
                    //  - the opening of a new subproof
                    //  - another inference
                    //    and a proof MAY end directly after an inference.
                    //  ---------------------
                    // in HALF-well-structured proofs, after an inference there should be either:
                    //  - the end of the subproof
                    //  - the opening of a new subproof
                    //  - another inference
                    //  - a premise (i.e. in this case an inference without justification)
                    //    and a proof MAY end directly after an inference.
                    if i + 1 < units.len() {
                        match units[i + 1] {
                            ProofUnit::NumberedProofLineInference(_)
                            | ProofUnit::SubproofOpen
                            | ProofUnit::SubproofClose => {}
                            ProofUnit::NumberedProofLinePremise(_) if check_only_half => {}
                            ProofUnit::FitchBarLine => {
                                return Err("Error: you cannot have a Fitch bar \
                                        after an inference. Maybe you are giving \
                                        justification for a premise?"
                                    .to_string());
                            }
                            ProofUnit::NumberedProofLinePremise(_) => {
                                return Err("Error: you cannot have a premise directly \
                                        after an inference. Maybe some justification is missing?"
                                    .to_string())
                            }
                        }
                    }
                }
                ProofUnit::NumberedProofLinePremise(num) => {
                    // in FULLY-well-structured proofs, after a premise there should be either:
                    //  - a Fitch bar line
                    //  - another premise
                    //       (only at the beginning of the proof, but we already check for
                    //        that in the ProofUnit::SubproofOpen arm of this match expression)
                    //    and a proof MUST NOT end directly after a premise.
                    //  ---------------------
                    //  in HALF-well-structured proofs, the requirements are the same, EXCEPT that
                    //  a proof MAY end directly after a premise, AND that a premise may also be
                    //  followed directly by an inference. (Because the user might forget to write
                    //  justification for something which is an inference, but the program sees it
                    //  as a premise in that case, but we don't want to give a fatal error so we
                    //  allow an inference to directly follow a premise)
                    if i + 1 == units.len() {
                        if !check_only_half {
                            return Err("Error: proof cannot end with a premise. Is \
                                   the justification for the last line missing?"
                                .to_string());
                        }
                    } else {
                        match units[i + 1] {
                            ProofUnit::FitchBarLine | ProofUnit::NumberedProofLinePremise(_) => {}
                            ProofUnit::NumberedProofLineInference(_) if check_only_half => {}
                            _ => {
                                return Err("Error: after a premise, there should be \
                                     a Fitch bar. Multiple premises are only allowed \
                                     at the beginning of the proof; subproofs should \
                                     have only exactly one premise."
                                    .to_string())
                            }
                        }
                    }
                }
            }
        }

        // last but not least: check that the line numbers are correct...
        // in a HALF-well-structured proof, line numbers must increase, but not necessarily in steps of one.
        // in a FULLY-well-structured proof, line numbers must increase in steps of one, and the first line number must be 1.
        let mut prev_num = 0;
        for unit in units {
            match unit {
                ProofUnit::NumberedProofLinePremise(num)
                | ProofUnit::NumberedProofLineInference(num) => {
                    if check_only_half && *num <= prev_num {
                        return Err(format!("Line numbers should be increasing! {num} is not bigger than {prev_num}..."));
                    }
                    if !check_only_half && *num != prev_num + 1 {
                        return Err(format!("Line numbers should start at one and increase by one at a time. (See between line {prev_num} and {num})"));
                    }
                    prev_num = *num;
                }
                _ => {}
            }
        }

        Ok(())
    }

    // converts proof lines to a vector of so-called ProofUnits which are useful during analysis.
    fn lines_to_units(proof_lines: &[ProofLine]) -> Result<Vec<ProofUnit>, String> {
        let mut units: Vec<ProofUnit> = vec![];
        let mut prev_depth = 1;

        // translate the proof to `ProofUnit`s
        for line in proof_lines {
            if line.depth == prev_depth + 1 {
                units.push(ProofUnit::SubproofOpen);
            } else if line.depth + 1 == prev_depth {
                units.push(ProofUnit::SubproofClose);
            } else if line.depth != prev_depth {
                return Err("Error: somewhere in this proof, there is an \'indentation/scope jump\' that is too big. You cannot open or close two subproofs in the same line.".to_string());
            }
            if let Some(line_num) = line.line_num {
                if line.is_premise {
                    units.push(ProofUnit::NumberedProofLinePremise(line_num));
                } else {
                    units.push(ProofUnit::NumberedProofLineInference(line_num));
                }
            }
            if line.is_fitch_bar_line {
                units.push(ProofUnit::FitchBarLine);
            }
            prev_depth = line.depth;
        }
        Ok(units)
    }

    // For half-well-structured proofs, we can compute `scope`, which is a Vec<(Vec<usize>,Vec<(usize,usize)>)>,
    // such that:
    // for all i in <line numbers corresponding to inferences (not premises) found in proof>:
    //   scope[i].0 == <the set of the line numbers which are referenceable by line i>
    //     and
    //   scope[i].1 == <the set of the subproofs i-j (stored as tuple (i,j)) which are referenceable by line i>
    //
    // the first index scope[0] is unused.
    fn determine_scope(units: &[ProofUnit]) -> Vec<(Vec<usize>, Vec<(usize, usize)>)> {
        let last_line_number: usize = match units.last() {
            Some(ProofUnit::NumberedProofLineInference(num))
            | Some(ProofUnit::NumberedProofLinePremise(num)) => *num,
            _ => {
                panic!("Oh no, this is a mistake by the developer. You should not try to determine the scope of a non-half-well-structured proof!");
            }
        };
        let mut scope: Vec<(Vec<usize>, Vec<(usize, usize)>)> =
            vec![(vec![], vec![]); last_line_number + 1];
        for i in 0..units.len() {
            if let ProofUnit::NumberedProofLineInference(num) = units[i] {
                // used to find referenceable single lines
                let mut depth: i32 = 0;

                // used to find referenceable subproofs
                let mut stack: Vec<usize> = vec![];

                for j in (0..i).rev() {
                    match units[j] {
                        ProofUnit::SubproofOpen => {
                            if depth > 0 {
                                depth -= 1;
                                let subproof_begin;
                                if let ProofUnit::NumberedProofLinePremise(s_begin) = units[j + 1] {
                                    subproof_begin = s_begin;
                                } else {
                                    panic!("This really should not happen. This is a mistake by the developer. Please contact me if you get this.");
                                }
                                let subproof_end = stack.pop().expect("This is a mistake by the developer. Please contact me if you get this.");
                                if stack.is_empty() {
                                    scope[num].1.push((subproof_begin, subproof_end));
                                }
                            }
                        }
                        ProofUnit::SubproofClose => {
                            depth += 1;
                            if let ProofUnit::NumberedProofLineInference(subproof_end) =
                                units[j - 1]
                            {
                                stack.push(subproof_end);
                            } else {
                                panic!("This really should not happen. This is a mistake by the developer. Please contact me if you get this.");
                            }
                        }
                        ProofUnit::NumberedProofLineInference(ref_num)
                        | ProofUnit::NumberedProofLinePremise(ref_num) => {
                            if depth == 0 {
                                scope[num].0.push(ref_num);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        scope
    }

    // checks whether line n1 can reference line n2.
    fn can_reference(&self, n1: usize, n2: usize) -> bool {
        self.scope[n1].0.contains(&n2)
    }

    // gets the wff at some requested line number, and if this line does not exist or
    // does not contain a sentence then this function will return an Err(). The function will also give
    // an Err() if the line is not allowed to be referenced from the referencing line (e.g. because
    // it is inside an already closed subproof).
    fn get_wff_at_line(
        &self,
        referencing_line: usize,
        requested_line: usize,
    ) -> Result<&Wff, String> {
        let li = self
            .lines
            .iter()
            .find(|l| l.line_num == Some(requested_line));
        if let Some(l) = li {
            if let Some(wff) = &l.sentence {
                if self.can_reference(referencing_line, requested_line) {
                    Ok(wff)
                } else {
                    Err(format!("Error: the justification of line {referencing_line} references line {requested_line}, but this is not allowed (for example because line {requested_line} is inside an already closed subproof)."))
                }
            } else {
                Err(format!("Error: in the justification of line {referencing_line}, line {requested_line} is being referred to, but this line does not contain a sentence."))
            }
        } else {
            Err(format!("Error: in the justification of line {referencing_line}, line {requested_line} is being referred to, but this line does not exist."))
        }
    }

    // checks the logical validity of a particular proof line within a proof
    // i.e., checks if the proof rule in the given line has been applied correctly
    // note that the provided proof line should exist in the proof, of course :)
    // (TODO call this function with line index instead)
    fn check_line(&self, line: &ProofLine) -> Result<(), String> {
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
                    let ref_wff = self.get_wff_at_line(curr_line_num, *n)?;
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
                        for i in 0..ns.len() {
                            if &conjs[i] != self.get_wff_at_line(curr_line_num, ns[i])? {
                                return Err(format!("In line {curr_line_num}, the conjunction introduction rule is used, but the {}\'th conjunct of that line is not the same as the sentence found in line {} (the {}\'th line referenced in the justification).",i+1,ns[i],i+1));
                            }
                        }
                        return Ok(());
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

        panic!(
        "Error: no idea what went wrong here. Please report this issue to the developer. Thanks!"
    )
    }
}
