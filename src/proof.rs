use crate::data::*;
use std::collections::HashSet;

/// [Scope] is a type which stores scoping information (like which lines can reference which
/// lines).
///
/// It is a `Vec<(Vec<usize>,Vec<(usize,usize)>)>`),
/// such that:
/// ```notrust
/// for all i in <line numbers corresponding to inferences (not premises) found in proof>:
///   scope[i].0 == <the set of the line numbers which are referenceable by line i>
///     and
///   scope[i].1 == <the set of the subproofs i-j (stored as tuple (i,j))
///                   which are referenceable by line i>
///   ```
///
/// The first index `scope[0]` is unused.
pub type Scope = Vec<(Vec<usize>, Vec<(usize, usize)>)>;

/// A [Proof] is a fundamental entity in this program. It contains important information that can
/// be used to assess whether the proof is correct.
///
/// Note that a [Proof] should always be
/// constructed using the [Proof::construct] function!!
///
/// Note that a [Proof] does not necessarily mean "a fully correct proof". If you want to assess
/// the full correctness of a [Proof], use [Proof::is_fully_correct].
pub struct Proof {
    ///  a vector containing all the [ProofLine]s this proof consists of,
    pub lines: Vec<ProofLine>,
    ///  a field that contains the [Scope] of the proof (it contains information which lines may
    /// reference which lines)
    pub scope: Scope,
    ///  a field containing the [ProofUnit]s: this is useful for assessing the validity of the
    /// structure of the proof.
    pub units: Vec<ProofUnit>,
    ///  a field which contains the set of strings that should be seen as a variable.
    pub allowed_variable_names: HashSet<String>,
}

/// An enum that is useful to look at the structure of a proof. This is useful for example when you
/// want to figure out which lines can reference which other lines. A proof can be represented
/// using a vector of [ProofUnit]s. One of the important differences between a vector [ProofLine]s
/// and a vector of [ProofUnit]s is that in a vector of [ProofLine]s, for each proof line the depth
/// is stored, and if you want to see where subproofs begin and end, you should look at the `depth`
/// of the [ProofLine]s. However, the opening and closing of a subproof are made much more explicit
/// when you have a vector of [ProofUnit]s. If you have some inference at depth 2, and then a
/// premise at depth 3 (i.e., a new subproof is opened), then between the corresponding
/// [ProofUnit]s for the two sentences, there will be a [ProofUnit::SubproofOpen].
///
/// Empty lines are not representable in terms of [ProofUnit]s (and this is also not necessary).
#[derive(Debug, PartialEq)]
pub enum ProofUnit {
    NumberedProofLineInference(usize), // usize is line number
    NumberedProofLinePremiseWithoutBoxedConstant(usize), // usize is line number
    NumberedProofLinePremiseWithBoxedConstant(usize), // usize is line number
    FitchBarLine,
    SubproofOpen,
    SubproofClose,
}

impl Proof {
    /// Given a vector of [ProofLine]s, this method constructs the proof. In case this method fails,
    /// it means a fatal error will need to be given, because if this method already fails then the
    /// proof is not even half-well-structured, and further analysis is impossible. After
    /// [Proof::construct]ing the proof, you should [Proof::is_fully_correct]() it. The combination of these two things
    /// allows you to assess the correctness of a proof.
    pub fn construct(
        proof_lines: Vec<ProofLine>,
        allowed_variable_names: HashSet<String>,
    ) -> Result<Proof, String> {
        let units = Self::lines_to_units(&proof_lines)?;
        Self::is_half_well_structured(&units)?; // check if proof is HALF-well-structured
        let scope = Self::determine_scope(&units);

        Ok(Proof {
            lines: proof_lines,
            scope,
            units,
            allowed_variable_names,
        })
    }

    /// From a vector of [ProofLine]s, this function generates a vector of [ProofUnit]s which are useful during analysis.
    fn lines_to_units(proof_lines: &[ProofLine]) -> Result<Vec<ProofUnit>, String> {
        let mut units: Vec<ProofUnit> = vec![];
        let mut prev_depth = 1;
        let mut last_line_num = 0;

        // translate the proof to `ProofUnit`s
        for line in proof_lines {
            if line.depth == prev_depth + 1 {
                units.push(ProofUnit::SubproofOpen);
            } else if line.depth + 1 == prev_depth {
                units.push(ProofUnit::SubproofClose);
            } else if line.depth != prev_depth {
                return Err(format!("near line {}, there is an \'indentation/scope jump\' that is too big. You cannot open or close two subproofs in the same line.",last_line_num+1));
            }
            if let Some(line_num) = line.line_num {
                last_line_num = line_num;
                if line.is_premise && line.constant_between_square_brackets.is_none() {
                    units.push(ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(line_num));
                } else if line.is_premise {
                    units.push(ProofUnit::NumberedProofLinePremiseWithBoxedConstant(line_num));
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

    /// This function computes the [Scope] of a proof.
    fn determine_scope(units: &[ProofUnit]) -> Scope {
        let last_line_number: usize = units
            .iter()
            .filter_map(|u| match u {
                ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(num)
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
                                if let ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(
                                    s_begin,
                                ) = units[j + 1]
                                {
                                    subproof_begin = s_begin;
                                } else if let ProofUnit::NumberedProofLinePremiseWithBoxedConstant(
                                    s_begin,
                                ) = units[j + 1]
                                {
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
                            } else if let ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(
                                subproof_end,
                            ) = units[j - 1]
                            {
                                stack.push(subproof_end);
                            } else if let ProofUnit::NumberedProofLinePremiseWithBoxedConstant(
                                subproof_end,
                            ) = units[j - 1]
                            {
                                stack.push(subproof_end);
                            } else {
                                panic!("This really should not happen. This is a mistake by the developer. Please contact me if you get this.");
                            }
                        }
                        ProofUnit::NumberedProofLineInference(ref_num)
                        | ProofUnit::NumberedProofLinePremiseWithBoxedConstant(ref_num)
                        | ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(ref_num) => {
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

    /// This function checks if a proof is HALF-well-structured.
    /// The reason that we make this distinction is because the validator algorithm does this:
    /// - (1) parse proof
    /// - (2) check that proof is HALF-well-structured
    /// - (3) check all lines of the proof
    /// - (4) check that proof is fully correct
    ///
    /// The point is that we want to give the user as helpful error messages as possible. We also
    /// want to be able to give the user several meaningful messages at the same time. But if a
    /// proof is not even half-well-structured, then it is not even possible to check all lines of
    /// it, so a FATAL error will be given, in which case all the other analysis does not happen.
    /// If the user has a HALF-structured (but not fully correct) proof, then it is still possible to
    /// perform the more detailed analysis in step 3, so we want that. In this case, the user will
    /// get meaningful error messages from all proof lines that are wrong, and that is better than
    /// only a fatal error when they for example just forget one justification somewhere.
    /// A notable allowed thing in half-well-structured proofs is having premises after the Fitch
    /// bar. Of course, this is not allowed in a fully correct proof, but here it means that we
    /// basically allow the user to not write a justification for the time being. In that case it
    /// will be parsed as a premise, so that's why we allow premises. This function won't complain
    /// about it, but of course, this will be checked when the proof is assessed for full correctness.
    fn is_half_well_structured(units: &[ProofUnit]) -> Result<(), String> {
        // traverse the `ProofUnit`s to check validity of the proof
        // basically, for each "proof unit", we check that the units after that are allowed.
        if units.is_empty() {
            return Err("Your proof appears to be empty.".to_string());
        }
        match units[0] {
            ProofUnit::FitchBarLine => {}
            ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(_) => {}
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
                    //  - a premise without boxed constant (inference for which the user didn't write justification yet)
                    //  - a new subproof
                    //    and a proof MUST NOT end with a Fitch bar line.
                    if i + 1 == units.len() {
                        return Err("The proof ends with a Fitch bar.".to_string());
                    } else {
                        match units[i + 1] {
                            ProofUnit::NumberedProofLineInference(_) => {}
                            ProofUnit::SubproofOpen => {}
                            ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(_) => {}
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
                        ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(_)
                        | ProofUnit::NumberedProofLinePremiseWithBoxedConstant(_) => {}
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
                    //  - a premise without boxed constant (inference for which user didn't write justification yet)
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
                            ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(_) => {}
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
                    //  - a premise without boxed constant (i.e. in this case an inference without justification)
                    //    and a proof MAY end directly after an inference.
                    if i + 1 < units.len() {
                        match units[i + 1] {
                            ProofUnit::NumberedProofLineInference(_)
                            | ProofUnit::SubproofOpen
                            | ProofUnit::SubproofClose => {}
                            ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(_) => {}
                            ProofUnit::FitchBarLine => {
                                return Err("Error: you cannot have a Fitch bar \
                                        after an inference. Maybe you are giving \
                                        justification for a premise?"
                                    .to_string());
                            }
                            ProofUnit::NumberedProofLinePremiseWithBoxedConstant(_) =>{
                                return Err("Error: a boxed constant can only be introduced in the premise of a subproof".to_owned())
                            }
                        }
                    }
                }
                ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(_) => {
                    // in HALF-well-structured proofs, after a premise w/out b.c. there should be either:
                    //  - a Fitch bar line
                    //  - another premise without boxed constant
                    //       (only at the beginning of the proof, but we already check for
                    //        that in the ProofUnit::SubproofOpen arm of this match expression)
                    //  - an inference
                    //  - a SubproofOpen
                    //  - a SubproofClose
                    //    and a proof MAY end directly after a premise without b.c.
                    //
                    if i + 1 < units.len() {
                        match units[i+1] {
                            ProofUnit::FitchBarLine | ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(_) | ProofUnit::NumberedProofLineInference(_) | ProofUnit::SubproofOpen | ProofUnit::SubproofClose => {}
                            ProofUnit::NumberedProofLinePremiseWithBoxedConstant(_) => {
                                return Err("Error: a boxed constant can only be introduced in the premise of a subproof".to_owned())
                            }
                        }
                    }
                }

                ProofUnit::NumberedProofLinePremiseWithBoxedConstant(_) => {
                    // in HALF-well-structured proofs, after a premise with b.c. there must be:
                    //  - a Fitch bar line
                    //    and a proof MUST NOT end directly after a premise with b.c.

                    if i + 1 >= units.len() {
                        return Err("Error: a proof cannot end with a premise.".to_owned());
                    }
                    match units[i + 1] {
                        ProofUnit::FitchBarLine => {}
                        _ => {
                            return Err(
                                "Error: after a premise, there should be a Fitch bar".to_owned()
                            );
                        }
                    }
                }
            }
        }

        // last but not least: check that the line numbers are correct...
        // they must start at 1 and increase in steps of 1
        let mut prev_num = 0;
        for unit in units {
            match unit {
                ProofUnit::NumberedProofLinePremiseWithBoxedConstant(num)
                | ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(num)
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
}
