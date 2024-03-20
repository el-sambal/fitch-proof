use crate::data::*;
use std::iter::zip;

type Scope = Vec<(Vec<usize>, Vec<(usize, usize)>)>;

// Name says it all :)
pub fn check_proof(proof_lines: Vec<ProofLine>) -> ProofResult {
    match Proof::construct(proof_lines) {
        Err(err) => ProofResult::FatalError(err),
        Ok(proof) => proof.is_fully_correct(),
    }
}

/* ------------------ PRIVATE -------------------- */

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
    scope: Scope,
    units: Vec<ProofUnit>,
}
impl Proof {
    // Given a vector of ProofLines, this method constructs the proof. In case this method fails,
    // it means a fatal error will need to be given, because if this method already fails then the
    // proof is not even half-well-structured, and further analysis is impossible. After
    // construct()ing the proof, you should proof.is_fully_correct() it. The combination of these two things
    // allows you to assess the correctness of a proof.
    fn construct(proof_lines: Vec<ProofLine>) -> Result<Proof, String> {
        let units = Self::lines_to_units(&proof_lines)?;
        Self::is_half_well_structured(&units)?; // check if proof is HALF-well-structured
        let scope = Self::determine_scope(&units);

        Ok(Proof {
            lines: proof_lines,
            scope,
            units,
        })
    }

    // returns a vector containing all line numbers which correspond to "premises"
    // that are found between a Fitch bar line and a SubproofOpen.
    // (these would be the inferences with missing justification, but they are parsed as premises)
    fn line_numbers_missing_justification(&self) -> Vec<usize> {
        let mut res = vec![]; // store what we're going to return
        let mut expect_justification = false;
        for i in 0..self.units.len() {
            match self.units[i] {
                ProofUnit::FitchBarLine => {
                    expect_justification = true;
                }
                ProofUnit::SubproofOpen => {
                    expect_justification = false;
                }
                ProofUnit::SubproofClose => {}
                ProofUnit::NumberedProofLineInference(_) => {}
                ProofUnit::NumberedProofLinePremise(num) => {
                    if expect_justification {
                        res.push(num);
                    }
                }
            }
        }

        res
    }

    // returns true iff the last line (that has a line number) is inside subproof
    fn last_line_is_inside_subproof(&self) -> bool {
        // unwrap should work, since this proof is half-well-structured, so it should contain some
        // line that contains a logical sentence or boxed constant (i.e. it has a line number).
        self.lines.iter().rev().find(|&pl| pl.sentence.is_some()).unwrap().depth > 1
    }

    // returns the line number of the last sentence of the proof.
    fn last_line_num(&self) -> usize {
        // unwrap should work, since this proof is half-well-structured, so it should contain some
        // line that contains a logical sentence or boxed constant (i.e. it has a line number).
        self.lines.iter().rev().find(|&pl| pl.line_num.is_some()).unwrap().line_num.unwrap()
    }

    // given a Proof (which 'by definition' is already HALF-well-structured,
    // otherwise its construct()or would have failed), checks if it is fully correct
    // (that is, each inference has a valid justification
    // and the last sentence is not inside a subproof).
    // Together with Proof::construct(), this is the method that you should run in
    // order to assess the validity of a proof.
    fn is_fully_correct(&self) -> ProofResult {
        let mut errors: Vec<String> = vec![]; // here we accumulate all errors
        for line in &self.lines {
            if let Err(err) = self.check_line(line) {
                println!("{err}");
                errors.push(err.to_string());
            }
        }

        errors.extend(
            self.line_numbers_missing_justification()
                .iter()
                .map(|n| format!("Line {n}: missing justification").to_string()),
        );

        if self.last_line_is_inside_subproof() {
            let lln = self.last_line_num();
            errors.push(format!("Line {lln}: last line of proof should not be inside subproof"));
        }

        if errors.is_empty() {
            ProofResult::Correct
        } else {
            errors.sort();
            ProofResult::Error(errors)
        }
    }

    // checks if a proof is HALF-well-structured.
    // The reason that we make this distinction is because the algorithm does this:
    // -> (1) parse proof
    // -> (2) check that proof is HALF-well-structured
    // -> (3) check all lines of the proof
    // -> (4) check that proof is fully correct
    // The point is that we want to give the user as helpful error messages as possible. We also
    // want to be able to give the user several meaningful messages at the same time. But if a
    // proof is not even half-well-structured, then it is not even possible to check all lines of
    // it, so a FATAL error will be given, in which case all the other analysis does not happen.
    // If the user has a HALF-structured (but not fully correct) proof, then it is still possible to
    // perform the more detailed analysis in step 3, so we want that. In this case, the user will
    // get meaningful error messages from all proof lines that are wrong, and that is better than
    // only a fatal error when they for example just forget one justification somewhere.
    // A notable allowed thing in half-well-structured proofs is having premises after the Fitch
    // bar. Of course, this is not allowed in a fully correct proof, but here it means that we
    // basically allow the user to not write a justification for the time being. In that case it
    // will be parsed as a premise, so that's why we allow premises. This function won't complain
    // about it, but of course, this will be checked when the proof is assessed for full correctness.
    fn is_half_well_structured(units: &[ProofUnit]) -> Result<(), String> {
        // traverse the `ProofUnit`s to check validity of the proof
        // basically, for each "proof unit", we check that the units after that are allowed.
        if units.is_empty() {
            return Err("Your proof appears to be empty.".to_string());
        }
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
                    // in HALF-well-structured proofs, a Fitch bar line may be succeeded by:
                    //  - an inference
                    //  - a premise (inference for which the user didn't write justification yet)
                    //  - a new subproof
                    //    and a proof MUST NOT end with a Fitch bar line.
                    if i + 1 == units.len() {
                        return Err("The proof ends with a Fitch bar.".to_string());
                    } else {
                        match units[i + 1] {
                            ProofUnit::NumberedProofLineInference(_) => {}
                            ProofUnit::SubproofOpen => {}
                            ProofUnit::NumberedProofLinePremise(_) => {}
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
                    // in HALF-well-structured proofs, after a subproof is opened, there must be:
                    //  - EXACTLY one numbered premise, FOLLOWED by a Fitch bar
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
                            return Err("Error: a subproof should have exactly one \
                                         premise, followed by a Fitch bar."
                                .to_string())
                        }
                    }
                }
                ProofUnit::SubproofClose => {
                    // in HALF-well-structured proofs, after a closed subproof there should be either:
                    //  - an inference
                    //  - a premise (inference for which user didn't write justification yet)
                    //  - a new subproof
                    //    and a proof MAY end directly after a closed subproof.
                    if i + 1 == units.len() {
                        if false {
                            return Err("Error: the proof ends with the closing of a subproof.\
                                       The last line of the proof should always be top-level."
                                .to_string());
                        }
                    } else {
                        match units[i + 1] {
                            ProofUnit::NumberedProofLineInference(_) => {}
                            ProofUnit::SubproofOpen => {}
                            ProofUnit::NumberedProofLinePremise(_) => {}
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
                            ProofUnit::NumberedProofLinePremise(_) => {}
                            ProofUnit::FitchBarLine => {
                                return Err("Error: you cannot have a Fitch bar \
                                        after an inference. Maybe you are giving \
                                        justification for a premise?"
                                    .to_string());
                            }
                        }
                    }
                }
                ProofUnit::NumberedProofLinePremise(_) => {
                    // in HALF-well-structured proofs, after a premise there should be either:
                    //  - a Fitch bar line
                    //  - another premise
                    //       (only at the beginning of the proof, but we already check for
                    //        that in the ProofUnit::SubproofOpen arm of this match expression)
                    //  - an inference
                    //  - a SubproofOpen
                    //  - a SubproofClose
                    //    and a proof MAY end directly after a premise.
                    //
                    //    No restrictions: this code block is effectively empty
                }
            }
        }

        // last but not least: check that the line numbers are correct...
        // they must start at 1 and increase in steps of 1
        let mut prev_num = 0;
        for unit in units {
            match unit {
                ProofUnit::NumberedProofLinePremise(num)
                | ProofUnit::NumberedProofLineInference(num) => {
                    if *num != 1 + prev_num {
                        return Err(format!("Line numbers are wrong; discrepancy between line {prev_num} and {num}..."));
                    }
                    prev_num = *num;
                }
                _ => {}
            }
        }

        Ok(()) // nice, proof is HALF-well-structured. we can now perform further analysis without
               // yielding a fatal error.
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
    fn determine_scope(units: &[ProofUnit]) -> Scope {
        let last_line_number: usize = units
            .iter()
            .filter_map(|u| match u {
                ProofUnit::NumberedProofLinePremise(num)
                | ProofUnit::NumberedProofLineInference(num) => Some(*num),
                _ => None,
            })
            .last()
            .unwrap();
        let mut scope: Scope = vec![(vec![], vec![]); last_line_number + 1];
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
                            } else if let ProofUnit::NumberedProofLinePremise(subproof_end) =
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
        let li = self.lines.iter().find(|l| l.line_num == Some(requested_line));
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

    // precondition: referencing_line is an existing line (and the scope needs to be computed
    // already, but that is always the case since we are working on an already-instantiated Proof
    // instance, and those cannot be created if their scope cannot be determined)
    fn get_subproof_at_lines(
        &self,
        referencing_line: usize,
        (subproof_begin, subproof_end): (usize, usize),
    ) -> Result<(&ProofLine, &ProofLine), String> {
        if self.scope[referencing_line].1.contains(&(subproof_begin, subproof_end)) {
            let s_begin = self.lines.iter().find(|l| l.line_num == Some(subproof_begin)).unwrap();
            // the unwrap should work, since `scope` should refer only to valid line numbers
            let s_end = self.lines.iter().find(|l| l.line_num == Some(subproof_end)).unwrap();
            Ok((s_begin, s_end))
        } else {
            Err(format!(
                "Line {referencing_line}: the referenced \
                        subproof {subproof_begin}-{subproof_end} is \
                        not in the scope of line {referencing_line}, \
                        or it does not exist."
            ))
        }
    }

    // checks the logical validity of a particular proof line within a proof
    // i.e., checks if the proof rule in the given line has been applied correctly.
    // Note that the provided proof line should exist in the proof, of course :)
    fn check_line(&self, line: &ProofLine) -> Result<(), String> {
        if line.sentence.is_none() || line.is_premise {
            return Ok(());
        }

        let mut curr_line_num: usize = usize::MAX;
        if let Some(line_num) = line.line_num {
            curr_line_num = line_num;
        }

        if let (Some(curr_wff), Some(just)) = (&line.sentence, &line.justification) {
            match just {
                Justification::Reit(n) => {
                    let ref_wff = self.get_wff_at_line(curr_line_num, *n)?;
                    if curr_wff == ref_wff {
                        Ok(())
                    } else {
                        Err(format!(
                            "Line {curr_line_num}, the \
                                           proof rule Reit is used, but the sentence \
                                           in this line is not the same as the sentence \
                                           in the referenced line."
                        ))
                    }
                }
                Justification::AndIntro(ns) => {
                    if let Wff::And(conjs) = curr_wff {
                        if ns.len() != conjs.len() {
                            return Err(format!(
                                "Line {curr_line_num}: \
                                               the conjuction introduction rule is used, \
                                               but the number of conjuncts in that line is \
                                               not equal to the number of referenced lines."
                            ));
                        }
                        for i in 0..ns.len() {
                            if &conjs[i] != self.get_wff_at_line(curr_line_num, ns[i])? {
                                return Err(format!(
                                    "Line {curr_line_num}: the conjunction \
                                             introduction rule is used, but the {}\'th \
                                             conjunct of that line is not the same as \
                                             the sentence found in line {} (the {}\'th \
                                             line referenced in the justification).",
                                    i + 1,
                                    ns[i],
                                    i + 1
                                ));
                            }
                        }
                        Ok(())
                    } else {
                        Err(format!(
                            "Line {curr_line_num}: the justification ∧Intro is \
                                used, but the top-level connective of this line is not ∧."
                        ))
                    }
                }
                Justification::AndElim(n) => {
                    let ref_wff = self.get_wff_at_line(curr_line_num, *n)?;
                    if let Wff::And(conjs) = ref_wff {
                        if conjs.iter().any(|conj| conj == curr_wff) {
                            Ok(())
                        } else {
                            Err(format!(
                                "Line {curr_line_num}: the justification \
                                               ∧Intro: {n} is used, but none of the \
                                               conjuncts in line {n} is identical \
                                               to line {curr_line_num}."
                            ))
                        }
                    } else {
                        Err(format!(
                            "Line {curr_line_num}: the justification \
                                    ∧Intro: {n} is used, but the top-level \
                                    connective of line {n} is not a conjunction."
                        ))
                    }
                }
                Justification::OrIntro(n) => {
                    let ref_wff = self.get_wff_at_line(curr_line_num, *n)?;
                    if let Wff::And(disjs) = ref_wff {
                        if disjs.iter().any(|disj| disj == ref_wff) {
                            Ok(())
                        } else {
                            Err(format!(
                                "Line {curr_line_num}: the justification \
                                               ∨Intro: {n} is used, but none of the \
                                               disjuncts in line {curr_line_num} is identical \
                                               to line {n}."
                            ))
                        }
                    } else {
                        Err(format!(
                            "Line {curr_line_num}: the justification \
                                    ∨Intro is used, but the top-level \
                                    connective of this line is not a disjunction."
                        ))
                    }
                }
                Justification::OrElim(n, subproofs) => {
                    if let Wff::Or(disjs) = self.get_wff_at_line(curr_line_num, *n)? {
                        if disjs.len() != subproofs.len() {
                            return Err(format!(
                                "Line {curr_line_num}: ∨Elim \
                                 is used, but the number of disjuncts \
                                 in this sentence is not equal to \
                                 the number of referenced subproofs."
                            ));
                        }
                        for (disj, subprf) in zip(disjs, subproofs) {
                            let (s_begin, s_end) =
                                self.get_subproof_at_lines(curr_line_num, *subprf)?;
                            if s_begin.constant_between_square_brackets.is_some()
                                || s_end.constant_between_square_brackets.is_some()
                            // the last sentence (s_end) in a subproof can
                            // never introduce a boxed constant, but user can input
                            // weird things, so dont remove the check for s_end.
                            {
                                return Err(format!(
                                    "Line {curr_line_num}: when using ∨Elim, \
                                 you cannot reference subproofs which \
                                 introduce a boxed constant."
                                ));
                            }
                            // unwrap should work, because the only case in which .sentence is
                            // None, is if it is a line that introduces a boxed constant, and we
                            // just checked for that.
                            let s_begin_wff = s_begin.sentence.as_ref().unwrap();
                            let s_end_wff = s_end.sentence.as_ref().unwrap();
                            if disj != s_begin_wff {
                                return Err(format!(
                                    "Line {curr_line_num}: ∨Elim \
                                 is used, but the premise one of the \
                                 referenced subproofs does not match the \
                                 corresponding disjunct of the referenced sentence. \
                                 Note that the subproofs should be referenced in the \
                                 order of their corresponding disjuncts."
                                ));
                            }
                            if s_end_wff != curr_wff {
                                return Err(format!(
                                    "Line {curr_line_num}: ∨Elim \
                                 is used, but not all referenced subproofs end with \
                                 the same sentence as in line {curr_line_num}."
                                ));
                            }
                        }
                        Ok(())
                    } else {
                        Err(format!(
                            "Line {curr_line_num}: ∨Elim \
                                 is used, but the top-level connective at \
                                 the first referenced line is not ∨."
                        ))
                    }
                }
                Justification::ImpliesIntro((n, m)) => {
                    if let Wff::Implies(a, b) = curr_wff {
                        let (s_begin, s_end) =
                            self.get_subproof_at_lines(curr_line_num, (*n, *m))?;
                        if let (Some(s_begin_wff), Some(s_end_wff)) =
                            (&s_begin.sentence, &s_end.sentence)
                        {
                            if **a != *s_begin_wff && **b == *s_end_wff {
                                Err(format!(
                                    "Line {curr_line_num}: →Intro is used, but \
                                the premise of the referenced subproof does not match the \
                                antecedent of the implication found in line {curr_line_num}."
                                ))
                            } else if **a == *s_begin_wff && **b != *s_end_wff {
                                Err(format!(
                                    "Line {curr_line_num}: →Intro is used, but \
                                the last sentence of the referenced subproof does not match the \
                                consequent of the implication found in line {curr_line_num}."
                                ))
                            } else if **a != *s_begin_wff && **b != *s_end_wff {
                                Err(format!(
                                    "Line {curr_line_num}: →Intro is used, but \
                                the premise and last sentence of the referenced subproof \
                                do not match the antecedent and the consequent, respectively, \
                                of the implication found in line {curr_line_num}."
                                ))
                            } else {
                                Ok(())
                            }
                        } else {
                            Err(format!(
                                "Line {curr_line_num}: when using →Intro, you \
                        cannot reference a subproof that introduces a boxed constant."
                            ))
                        }
                    } else {
                        Err(format!(
                            "Line {curr_line_num}: →Intro is used, but \
                            the top-level connective of this sentence \
                            is not an implication."
                        ))
                    }
                }
                Justification::ImpliesElim(n, m) => {
                    if let Wff::Implies(wff1, wff2) = self.get_wff_at_line(curr_line_num, *n)? {
                        let wff_m = self.get_wff_at_line(curr_line_num, *m)?;
                        if *wff_m == **wff1 && **wff2 == *curr_wff {
                            Ok(())
                        } else {
                            Err(format!(
                                "Line {curr_line_num}: the rule \
                                               →Elim is wrongly used."
                            ))
                        }
                    } else {
                        Err(format!(
                            "Line {curr_line_num}: the rule \
                                           →Elim: {n}, {m} is used, but the top-level \
                                           connective of line {n} is not an implication."
                        ))
                    }
                }
                Justification::NotIntro((n, m)) => {
                    let (s_begin, s_end) = self.get_subproof_at_lines(curr_line_num, (*n, *m))?;
                    if let Wff::Not(negated) = curr_wff {
                        if let (Some(s_begin_wff), Some(s_end_wff)) =
                            (&s_begin.sentence, &s_end.sentence)
                        {
                            if **negated == *s_begin_wff {
                                if *s_end_wff == Wff::Bottom {
                                    Ok(())
                                } else {
                                    Err(format!(
                                        "Line {curr_line_num}: ¬Intro is used, \
                                    but the last sentence in the referenced \
                                    subproof is not ⊥."
                                    ))
                                }
                            } else {
                                Err(format!(
                                    "Line {curr_line_num}: ¬Intro is \
                                            used, but the negation of the premise \
                                            of the referenced subproof does \
                                            not match this line."
                                ))
                            }
                        } else {
                            Err(format!(
                                "Line {curr_line_num}: ¬Intro is \
                            used, but the referenced subproof is not \
                            of the proper form. You cannot use ¬Intro \
                            on a subproof that introduces a boxed constant."
                            ))
                        }
                    } else {
                        Err(format!(
                            "Line {curr_line_num}: ¬Intro is used, \
                                        but the top-level connective is not ¬."
                        ))
                    }
                }
                Justification::NotElim(n) => {
                    if let Wff::Not(negd_wff) = self.get_wff_at_line(curr_line_num, *n)? {
                        if let Wff::Not(negd_negd_wff) = &**negd_wff {
                            if **negd_negd_wff == *curr_wff {
                                return Ok(());
                            }
                        }
                    }
                    Err(format!("Line {curr_line_num}: ¬Elim is used improperly."))
                }
                Justification::BottomIntro(n, m) => {
                    let wff1 = self.get_wff_at_line(curr_line_num, *n)?;
                    let wff2 = self.get_wff_at_line(curr_line_num, *m)?;
                    if let Wff::Not(negd_wff) = wff2 {
                        if *wff1 == **negd_wff {
                            return Ok(());
                        }
                    }
                    Err(format!(
                        "Line {curr_line_num}: ⊥Intro is used, \
                                       but the second referenced line is not the negation \
                                       of the first referenced line."
                    ))
                }
                Justification::BottomElim(n) => {
                    if let Wff::Bottom = self.get_wff_at_line(curr_line_num, *n)? {
                        Ok(())
                    } else {
                        Err(format!(
                            "Line {curr_line_num}: ⊥Elim is \
                                    used, but the referenced line is not ⊥."
                        ))
                    }
                }
                Justification::EqualsIntro(_) => {
                    todo!()
                }
                Justification::EqualsElim(_,_) => {
                    todo!()
                }
                Justification::ForallIntro((_, _)) => {
                    todo!()
                }
                Justification::ForallElim(_) => {
                    todo!()
                }
                Justification::ExistsIntro(_) => {
                    todo!()
                }
                Justification::ExistsElim(_, (_, _)) => {
                    todo!()
                }
            }
        } else {
            panic!(
                "If you reach this code, then there was \
                   some sentence that had no justification \
                   but was not parsed as a premise... This \
                   should be impossible."
            );
        }
    }
}
