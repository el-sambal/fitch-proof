use crate::data::*;
use std::collections::HashSet;
use std::iter::once;
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

#[derive(Debug, PartialEq)]
enum ProofUnit {
    NumberedProofLineInference(usize),
    NumberedProofLinePremiseWithoutBoxedConstant(usize),
    NumberedProofLinePremiseWithBoxedConstant(usize),
    FitchBarLine,
    SubproofOpen,
    SubproofClose,
}

// should be always constructed using the construct() method!!!!!
struct Proof {
    lines: Vec<ProofLine>,
    scope: Scope,
    units: Vec<ProofUnit>,
    allowed_variable_names: HashSet<String>,
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
            allowed_variable_names: HashSet::from([
                "x".to_string(),
                "y".to_string(),
                "z".to_string(),
                "u".to_string(),
            ]),
        })
    }

    // given a Proof (which 'by definition' is already HALF-well-structured,
    // otherwise its construct()or would have failed), checks if it is fully correct
    // (that is, each inference has a valid justification
    // and the last sentence is not inside a subproof).
    // Together with Proof::construct(), this is the method that you should run in
    // order to assess the validity of a proof.
    fn is_fully_correct(&self) -> ProofResult {
        let mut errors: Vec<String> = vec![]; // here we accumulate all errors

        // check that user applied proof rule correctly everywhere
        for line in &self.lines {
            if let Err(err) = self.check_line(line) {
                println!("{err}");
                errors.push(err.to_string());
            }
        }

        // check that proof starts with zero or more premises, followed by a Fitch bar
        if !self.units.iter().any(|u| *u == ProofUnit::FitchBarLine)
            || !self
                .units
                .iter()
                .take_while(|u| **u != ProofUnit::FitchBarLine)
                .all(|u| matches!(*u, ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(..)))
        {
            errors.push(
                "Each proof should start start with zero or more premises, followed by a Fitch bar"
                    .to_string(),
            );
        }

        // check that all inferences have justification
        errors.extend(
            self.line_numbers_missing_justification()
                .iter()
                .map(|n| format!("Line {n}: missing justification").to_string()),
        );

        // check that all variables are bound, that user doesn't have nested quantifiers over the
        // same variable and that users don't quantify over a constant
        errors.extend(
            self.lines
                .iter()
                .filter(|line| line.sentence.is_some())
                .map(|line| {
                    self.check_variable_scoping_issues(
                        line.sentence.as_ref().unwrap(),
                        line.line_num.unwrap(),
                    )
                })
                .filter(|r| r.is_err())
                .map(|r| r.unwrap_err()),
        );

        // check that user doesn't use boxed constant outside the subproof and that user does not
        // introduce the same boxed constant twice in nested subproofs, and that boxed constants
        // are actually constants (not variables or predicates or ...)
        if let Err(errs) = self.check_boxed_constant_outside_subproof() {
            errors.extend(errs);
        }

        // check that last line is top-level
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
                ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(num)
                | ProofUnit::NumberedProofLinePremiseWithBoxedConstant(num) => {
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

    // This function gives you the ProofLine at line number line_num. It does not care about who
    // referenced this line, and scope issues and such, it just gives it to you. This function
    // panics if the line number does not exist within the proof.
    fn get_proofline_at_line_unsafe(&self, line_num: usize) -> &ProofLine {
        self.lines.iter().find(|x| x.line_num.is_some() && x.line_num.unwrap() == line_num).unwrap()
    }

    fn check_boxed_constant_outside_subproof(&self) -> Result<(), Vec<String>> {
        let mut errors: Vec<String> = vec![];

        // step 1: check which boxed constants exist within the proof
        let boxed_consts: HashSet<_> = self
            .lines
            .iter()
            .filter_map(|line| line.constant_between_square_brackets.clone())
            .collect();

        // step 2: let's also give warnings if the user puts a variable in a box (not a constant)
        errors.extend(
            self.lines
                .iter()
                .filter(|line| line.constant_between_square_brackets.is_some())
                .filter_map(|line| {
                    if self.term_is_constant(
                        line.constant_between_square_brackets.as_ref().unwrap().clone(),
                    ) {
                        None
                    } else {
                        Some(format!("Line {}: a boxed constant cannot be a variable (should not have the name of a variable).", line.line_num.unwrap()))
                    }
                }),
        );

        // step 3: iterate over proof units and see if boxed constants only get used when allowed
        // keep a stack of which boxed constants are in scope:
        let mut currently_in_scope: Vec<Option<Term>> = vec![];
        for i in 0..self.units.len() {
            match self.units[i] {
                ProofUnit::FitchBarLine => {}
                ProofUnit::NumberedProofLinePremiseWithBoxedConstant(num) => {
                    let new_boxed_const =
                        &self.get_proofline_at_line_unsafe(num).constant_between_square_brackets;

                    // before we add the new variable to current scope,
                    // test that it was not already in scope:
                    if currently_in_scope.contains(new_boxed_const) {
                        errors.push(format!("Line {num}: you cannot introduce the same boxed constant twice in nested subproofs"));
                    }

                    currently_in_scope.push(new_boxed_const.clone());

                    if let Some(wff) = &self.get_proofline_at_line_unsafe(num).sentence {
                        match check_wff_not_contain_out_of_scope_boxed_consts(
                            wff,
                            &currently_in_scope,
                            &boxed_consts,
                            num,
                        ) {
                            Ok(_) => {}
                            Err(err) => errors.push(err),
                        }
                    }
                }
                ProofUnit::NumberedProofLinePremiseWithoutBoxedConstant(num) => {
                    currently_in_scope.push(None);

                    let prfln = self.get_proofline_at_line_unsafe(num);
                    if let Err(err) = check_wff_not_contain_out_of_scope_boxed_consts(
                        prfln.sentence.as_ref().unwrap(),
                        &currently_in_scope,
                        &boxed_consts,
                        num,
                    ) {
                        errors.push(err);
                    }
                }
                ProofUnit::NumberedProofLineInference(num) => {
                    let prfln = self.get_proofline_at_line_unsafe(num);
                    if let Err(err) = check_wff_not_contain_out_of_scope_boxed_consts(
                        prfln.sentence.as_ref().unwrap(),
                        &currently_in_scope,
                        &boxed_consts,
                        num,
                    ) {
                        errors.push(err);
                    }
                }
                ProofUnit::SubproofClose => {
                    currently_in_scope.pop();
                }
                ProofUnit::SubproofOpen => {}
            }
        }

        // if wff contains a *constant* which is in the global set of boxed constants (all_boxeds), but not in
        // the current scope, then return Err. Otherwise Ok.
        fn check_wff_not_contain_out_of_scope_boxed_consts(
            wff: &Wff,
            curr_scope: &[Option<Term>],
            all_boxeds: &HashSet<Term>,
            line_num: usize,
        ) -> Result<(), String> {
            fn check_term_not_contain_out_of_scope_boxed_consts(
                term: &Term,
                curr_scope: &[Option<Term>],
                all_boxeds: &HashSet<Term>,
                line_num: usize,
            ) -> Result<(), String> {
                match term {
                    Term::Atomic(_) => {
                        if all_boxeds.contains(term)
                            && !curr_scope.iter().filter_map(|x| x.as_ref()).any(|t| t == term)
                        {
                            Err(format!("Line {line_num}: it is not allowed to use a boxed constant outside the subproof that defines it"))
                        } else {
                            Ok(())
                        }
                    }
                    Term::FuncApp(_, args) => args.iter().try_for_each(|a| {
                        check_term_not_contain_out_of_scope_boxed_consts(
                            a, curr_scope, all_boxeds, line_num,
                        )
                    }),
                }
            }
            match wff {
                Wff::Bottom => Ok(()),
                Wff::And(li) | Wff::Or(li) => li.iter().try_for_each(|w| {
                    check_wff_not_contain_out_of_scope_boxed_consts(
                        w, curr_scope, all_boxeds, line_num,
                    )
                }),
                Wff::Implies(a, b) | Wff::Bicond(a, b) => {
                    check_wff_not_contain_out_of_scope_boxed_consts(
                        a, curr_scope, all_boxeds, line_num,
                    )
                    .and(check_wff_not_contain_out_of_scope_boxed_consts(
                        b, curr_scope, all_boxeds, line_num,
                    ))
                }
                Wff::Not(w) => check_wff_not_contain_out_of_scope_boxed_consts(
                    w, curr_scope, all_boxeds, line_num,
                ),
                Wff::Forall(_, w) | Wff::Exists(_, w) => {
                    check_wff_not_contain_out_of_scope_boxed_consts(
                        w, curr_scope, all_boxeds, line_num,
                    )
                }
                Wff::Atomic(_) => Ok(()),
                Wff::PredApp(_, args) => args.iter().try_for_each(|t| {
                    check_term_not_contain_out_of_scope_boxed_consts(
                        t, curr_scope, all_boxeds, line_num,
                    )
                }),
                Wff::Equals(s, t) => check_term_not_contain_out_of_scope_boxed_consts(
                    s, curr_scope, all_boxeds, line_num,
                )
                .and(check_term_not_contain_out_of_scope_boxed_consts(
                    t, curr_scope, all_boxeds, line_num,
                )),
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    // check that all variables are bound, that user doesn't have nested quantifiers over the
    // same variable and that users don't quantify over a constant
    fn check_variable_scoping_issues(&self, wff: &Wff, line_num: usize) -> Result<(), String> {
        fn check_variable_scoping_issues_helper(
            proof: &Proof,
            wff: &Wff,
            line_num: usize,
            bound_vars_in_scope: &mut Vec<String>,
        ) -> Result<(), String> {
            match wff {
                Wff::Bottom => Ok(()),
                Wff::Atomic(_) => Ok(()),
                Wff::PredApp(_, args) => args.iter().try_for_each(|a| {
                    check_variable_scoping_issues_helper_term(
                        proof,
                        a,
                        line_num,
                        bound_vars_in_scope,
                    )
                }),
                Wff::And(li) | Wff::Or(li) => li.iter().try_for_each(|x| {
                    check_variable_scoping_issues_helper(proof, x, line_num, bound_vars_in_scope)
                }),
                Wff::Implies(w1, w2) | Wff::Bicond(w1, w2) => {
                    check_variable_scoping_issues_helper(proof, w1, line_num, bound_vars_in_scope)
                        .and(check_variable_scoping_issues_helper(
                            proof,
                            w2,
                            line_num,
                            bound_vars_in_scope,
                        ))
                }
                Wff::Not(w) => {
                    check_variable_scoping_issues_helper(proof, w, line_num, bound_vars_in_scope)
                }
                Wff::Equals(t1, t2) => check_variable_scoping_issues_helper_term(
                    proof,
                    t1,
                    line_num,
                    bound_vars_in_scope,
                )
                .and(check_variable_scoping_issues_helper_term(
                    proof,
                    t2,
                    line_num,
                    bound_vars_in_scope,
                )),
                Wff::Forall(var, wff) | Wff::Exists(var, wff) => {
                    if !proof.allowed_variable_names.contains(var) {
                        Err(format!("Line {line_num}: you can only quantify over a variable, not over a constant."))
                    } else if bound_vars_in_scope.contains(var) {
                        Err(format!(
                            "Line {line_num}: this line contains \
                                       two nested quantifiers over the same variable."
                        ))
                    } else {
                        bound_vars_in_scope.push(var.to_string());
                        let res = check_variable_scoping_issues_helper(
                            proof,
                            wff,
                            line_num,
                            bound_vars_in_scope,
                        );
                        bound_vars_in_scope.pop();
                        res
                    }
                }
            }
        }

        fn check_variable_scoping_issues_helper_term(
            proof: &Proof,
            term: &Term,
            line_num: usize,
            bound_vars_in_scope: &mut Vec<String>,
        ) -> Result<(), String> {
            match term {
                Term::Atomic(str) => {
                    if proof.allowed_variable_names.contains(str)
                        && !bound_vars_in_scope.contains(str)
                    {
                        Err(format!("Line {line_num}: this line contains unbound variables."))
                    } else {
                        Ok(())
                    }
                }
                Term::FuncApp(_, args) => args.iter().try_for_each(|a| {
                    check_variable_scoping_issues_helper_term(
                        proof,
                        a,
                        line_num,
                        bound_vars_in_scope,
                    )
                }),
            }
        }
        check_variable_scoping_issues_helper(self, wff, line_num, &mut vec![])
    }

    // this function returns the "arity set" for a proof. This is a HashSet containing instances of
    // (name,arity), where name can be the name of any constant, funtion symbol, atomic proposition
    // or predicate, and arity is its arity. Note that the arity of constants and atomic
    // propositions is defined to be 0. Note that variables are not included in the arity set.
    //
    // Note that if you find for example both f(x,x) and f(x,x,x) in the same proof, then BOTH the
    // entries ("f", 2) and ("f", 3) will be included in the arity set.
    fn get_arity_set(&self) -> HashSet<(String, usize)> {
        fn get_arity_set_term(proof: &Proof, term: &Term) -> HashSet<(String, usize)> {
            match term {
                Term::Atomic(str) => {
                    if proof.allowed_variable_names.contains(str) {
                        HashSet::from([])
                    } else {
                        HashSet::from([(str.to_owned(), 0)])
                    }
                }
                Term::FuncApp(str, args) => args
                    .iter()
                    .map(|t| get_arity_set_term(proof, t))
                    .chain(std::iter::once(HashSet::from([(str.to_owned(), 0)])))
                    .flat_map(|it| it.clone())
                    .collect(),
            }
        }
        fn get_arity_set_wff(proof: &Proof, wff: &Wff) -> HashSet<(String, usize)> {
            match wff {
                Wff::Bottom => HashSet::from([]),
                Wff::And(li) | Wff::Or(li) => {
                    li.iter().flat_map(|t| get_arity_set_wff(proof, t)).collect()
                }
                Wff::Forall(_, w) | Wff::Exists(_, w) | Wff::Not(w) => get_arity_set_wff(proof, w),
                Wff::Bicond(w1, w2) | Wff::Implies(w1, w2) => get_arity_set_wff(proof, w1)
                    .into_iter()
                    .chain(get_arity_set_wff(proof, w2))
                    .collect(),
                Wff::Equals(t1, t2) => get_arity_set_term(proof, t1)
                    .into_iter()
                    .chain(get_arity_set_term(proof, t2))
                    .collect(),
                Wff::PredApp(str, args) => args
                    .iter()
                    .map(|t| get_arity_set_term(proof, t))
                    .chain(std::iter::once(HashSet::from([(str.to_owned(), 0)])))
                    .flatten()
                    .collect(),
                Wff::Atomic(str) => HashSet::from([(str.to_owned(), 0)]),
            }
        }
        self.lines
            .iter()
            .by_ref()
            .filter_map(|line| line.sentence.as_ref())
            .flat_map(|t| get_arity_set_wff(self, t))
            .chain(
                // also include boxed constants in arity set!
                self.lines
                    .iter()
                    .by_ref()
                    .filter_map(|line| line.constant_between_square_brackets.as_ref())
                    .map(|c| match c {
                        Term::Atomic(str) => (str.to_owned(), 0),
                        Term::FuncApp(..) => panic!("boxed constant cannot be FuncApp"),
                    }),
            )
            .collect()
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

    // converts proof lines to a vector of so-called ProofUnits which are useful during analysis.
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
                } else if requested_line < referencing_line {
                    Err(format!("Line {referencing_line}: line {requested_line} is referenced in the justification, but this is not allowed, because line {requested_line} is inside an already closed subproof."))
                } else {
                    Err(format!("Line {referencing_line}: line {requested_line} is referenced in the justification, but this is not allowed, because line {requested_line} does not come before line {referencing_line}."))
                }
            } else {
                Err(format!("Line {referencing_line}: line {requested_line} is being referenced in the justification, but that line does not contain a sentence."))
            }
        } else {
            Err(format!("Line {referencing_line}: line {requested_line} is being referenced in the justification, but that line does not exist."))
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
                    if let Wff::Or(disjs) = curr_wff {
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
                        if let (Some(s_begin_wff), Some(s_end_wff), None) = (
                            &s_begin.sentence,
                            &s_end.sentence,
                            &s_begin.constant_between_square_brackets,
                        ) {
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
                Justification::BicondIntro((sb1, se1), (sb2, se2)) => {
                    if let Wff::Bicond(p, q) = curr_wff {
                        let (s_begin1, s_end1) =
                            self.get_subproof_at_lines(curr_line_num, (*sb1, *se1))?;
                        let (s_begin2, s_end2) =
                            self.get_subproof_at_lines(curr_line_num, (*sb2, *se2))?;
                        if let (
                            Some(s_begin_wff1),
                            Some(s_end_wff1),
                            Some(s_begin_wff2),
                            Some(s_end_wff2),
                            None,
                            None,
                        ) = (
                            &s_begin1.sentence,
                            &s_end1.sentence,
                            &s_begin2.sentence,
                            &s_end2.sentence,
                            &s_begin1.constant_between_square_brackets,
                            &s_begin2.constant_between_square_brackets,
                        ) {
                            if **p == *s_begin_wff1
                                && **q == *s_end_wff1
                                && **p == *s_end_wff2
                                && **q == *s_begin_wff2
                            {
                                Ok(())
                            } else {
                                Err(format!("Line {curr_line_num}: when using ↔Intro to infer P↔Q, you must first cite the subproof that proves P→Q, and then the subproof that proves Q→P."))
                            }
                        } else {
                            Err(format!("Line {curr_line_num}: when using ↔Intro, you cannot reference a subproof that introduces a boxed constant."))
                        }
                    } else {
                        Err(format!("Line {curr_line_num}: ↔Intro is used, but the top-level connective of this sentence is not a bi-implication."))
                    }
                }
                Justification::BicondElim(n, m) => {
                    if let Wff::Bicond(wff1, wff2) = self.get_wff_at_line(curr_line_num, *n)? {
                        let wff_m = self.get_wff_at_line(curr_line_num, *m)?;
                        if (*wff_m == **wff1 && **wff2 == *curr_wff)
                            || (*wff_m == **wff2 && **wff1 == *curr_wff)
                        {
                            Ok(())
                        } else {
                            Err(format!("Line {curr_line_num}: the rule ↔Elim is wrongly used."))
                        }
                    } else {
                        Err(format!("Line {curr_line_num}: the rule ↔Elim: {n}, {m} is used, but the top-level connective of line {n} is not a bi-implication."))
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
                                       of the first referenced line"
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
                Justification::EqualsIntro => {
                    if let Wff::Equals(term1, term2) = curr_wff {
                        if term1 == term2 {
                            return Ok(());
                        }
                    }
                    Err(format!("Line {curr_line_num}: =Intro is wrongly used"))
                }
                Justification::EqualsElim(n, m) => {
                    if let Wff::Equals(subst_old, subst_new) =
                        self.get_wff_at_line(curr_line_num, *m)?
                    {
                        if substitution_applied_wff_one_or_more_times(
                            self.get_wff_at_line(curr_line_num, *n)?,
                            curr_wff,
                            (subst_old, subst_new),
                        ) {
                            Ok(())
                        } else {
                            Err(format!(
                                "Line {curr_line_num}: the rule =Elim:{n},{m} \
                            is used, but is is impossible to obtain line {curr_line_num} \
                            from line {n} by substituting one or more occurrences of <term1> by \
                            <term2>, where line {m} is <term1> = <term2>"
                            ))
                        }
                    } else {
                        Err(format!(
                            "Line {curr_line_num}: the rule =Elim:{n},{m} \
                                    is used, but line {m} is not of the form <term1> = <term2>"
                        ))
                    }
                }
                Justification::ForallIntro((sb, se)) => {
                    let Wff::Forall(var, forall_curr_wff) = curr_wff else {
                        return Err(format!("Line {curr_line_num}: the rule ∀Intro is used, but this sentence is not universally quantified at the top-level"));
                    };
                    let (s_begin, s_end) = self.get_subproof_at_lines(curr_line_num, (*sb, *se))?;
                    let Some(boxed_const @ Term::Atomic(bc)) =
                        &s_begin.constant_between_square_brackets
                    else {
                        return Err(format!("Line {curr_line_num}: the rule ∀Intro is used, but the referenced subproof does not have a boxed constant"));
                    };
                    if s_begin.sentence.is_some() {
                        return Err(format!("Line {curr_line_num}: when using ∀Intro, the premise of the referenced subproof should consist of solely a boxed constant, without a sentence"));
                    }
                    if apply_trivial_substitution_everywhere_to_wff(
                        forall_curr_wff,
                        (&Term::Atomic(var.to_string()), boxed_const),
                    ) != *s_end.sentence.as_ref().unwrap()
                    {
                        return Err(format!("Line {curr_line_num}: the rule ∀Intro:{sb}-{se} is used, but if all occurrences of {var} in the quantified part of line {curr_line_num} are replaced by {bc}, then one does not obtain the sentence in line {se}, but this should be the case"));
                    }

                    Ok(())
                }
                Justification::ForallElim(n) => {
                    if let Wff::Forall(var, ref_wff) = self.get_wff_at_line(curr_line_num, *n)? {
                        if let Some((term1, term2)) =
                            find_possible_trivial_substitution_wff(ref_wff, curr_wff)
                        {
                            if apply_trivial_substitution_everywhere_to_wff(
                                ref_wff,
                                (&term1, &term2),
                            ) == *curr_wff
                                && Term::Atomic(var.to_string()) == term1
                            {
                                return if self.is_closed_term(term2) {
                                    Ok(())
                                } else {
                                    Err(format!(
                                        "Line {curr_line_num}: the rule ∀Elim:{n} is used, \
                                                but you did not substitute a *closed* term for \
                                                all occurrences of the variable {var} in line {n}"
                                    ))
                                };
                            }
                        }
                        Err(format!(
                            "Line {curr_line_num}: the rule \
                                        ∀Elim:{n} is used, but there is no \
                                        appropriate substitution between line \
                                        {n} and line {curr_line_num}"
                        ))
                    } else {
                        Err(format!(
                            "Line {curr_line_num}: the justification \
                                    ∀Elim:{n} is used, but line {n} is not a \
                                    universally quantified sentence at the top level"
                        ))
                    }
                }
                Justification::ExistsIntro(n) => {
                    if let Wff::Exists(var, exists_curr_wff) = curr_wff {
                        let ref_wff = self.get_wff_at_line(curr_line_num, *n)?;
                        if let Some((term1, term2)) =
                            find_possible_trivial_substitution_wff(exists_curr_wff, ref_wff)
                        {
                            if substitution_applied_wff_zero_or_more_times(
                                exists_curr_wff,
                                ref_wff,
                                (&term1, &term2),
                            ) && Term::Atomic(var.to_string()) == term1
                            {
                                return if self.is_closed_term(term2) {
                                    Ok(())
                                } else {
                                    Err(format!(
                                        "Line {curr_line_num}: the rule ∃Intro:{n} is \
                                                used, but the term in line {n} that you \
                                                substitute {var} for in line {curr_line_num} \
                                                is not a *closed* term"
                                    ))
                                };
                            }
                        }
                        if **exists_curr_wff == *ref_wff {
                            return Ok(());
                        }
                        Err(format!(
                            "Line {curr_line_num}: the rule \
                                        ∃Intro:{n} is used, but there is no \
                                        appropriate substitution between line \
                                        {n} and line {curr_line_num}"
                        ))
                    } else {
                        Err(format!(
                            "Line {curr_line_num}: the justification \
                                    ∃Intro:{n} is used, but line {curr_line_num} is not an \
                                    existentially quantified sentence at the top level"
                        ))
                    }
                }
                Justification::ExistsElim(n, (sb, se)) => {
                    let ref_wff = self.get_wff_at_line(curr_line_num, *n)?;
                    let (s_begin, s_end) = self.get_subproof_at_lines(curr_line_num, (*sb, *se))?;
                    let Wff::Exists(var, exists_ref_wff) = ref_wff else {
                        return Err(format!("Line {curr_line_num}: the rule ∃Elim:{n},{sb}-{se} is used, but the sentence at line {n} is not an existentially quantified sentence at the top-level"));
                    };

                    let Some(bc_term @ Term::Atomic(bc)) =
                        &s_begin.constant_between_square_brackets
                    else {
                        return Err(format!("Line {curr_line_num}: the rule ∃Elim:{n},{sb}-{se} is used, but the referenced subproof does not introduce a boxed constant."));
                    };

                    if s_begin.sentence.is_none() {
                        return Err(format!("Line {curr_line_num}: the rule ∃Elim:{n},{sb}-{se} is used, but line {sb} contains only a boxed constant; when using ∃Elim, it should contain both a boxed constant and a sentence"));
                    }
                    if apply_trivial_substitution_everywhere_to_wff(
                        exists_ref_wff,
                        (&Term::Atomic(var.to_string()), &bc_term),
                    ) == *s_begin.sentence.as_ref().unwrap()
                    {
                        if s_end.sentence.as_ref().unwrap() == curr_wff {
                            Ok(())
                        } else {
                            Err(format!("Line {curr_line_num}: the rule ∃Elim:{n},{sb}-{se} is used, but the sentence in line {se} is not the same as the sentence in line {curr_line_num}"))
                        }
                    } else {
                        Err(format!("Line {curr_line_num}: the rule ∃Elim:{n},{sb}-{se} is used, but if one substitutes {bc} for all free occurences of {var} in the quantified part of the sentence in line {n}, one does not obtain the sentence found in line {sb}, but this should be the case"))
                    }
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

    fn term_is_constant(&self, term: Term) -> bool {
        match term {
            Term::FuncApp(..) => false,
            Term::Atomic(str) => !self.allowed_variable_names.contains(&str),
        }
    }

    fn is_closed_term(&self, term: Term) -> bool {
        match term {
            Term::Atomic(str) => !self.allowed_variable_names.contains(&str),
            Term::FuncApp(_, args) => args.iter().all(|a| self.is_closed_term(a.clone())),
        }
    }
}

// returns true iff term b can be obtained from term a by applying
// the substitution subst *zero or more* times.
fn substitution_applied_term_zero_or_more_times(a: &Term, b: &Term, subst: (&Term, &Term)) -> bool {
    match (&a, &b) {
        (Term::Atomic(a_name), Term::Atomic(b_name)) => a_name == b_name || subst == (a, b),
        (Term::Atomic(_), Term::FuncApp(..)) => subst == (a, b),
        (Term::FuncApp(..), Term::Atomic(_)) => subst == (a, b),
        (Term::FuncApp(f1_name, args1), Term::FuncApp(f2_name, args2)) => {
            (subst) == (a, b)
                || (f1_name == f2_name
                    && args1.len() == args2.len()
                    && zip(args1, args2).all(|(arg1, arg2)| {
                        substitution_applied_term_zero_or_more_times(arg1, arg2, subst)
                    }))
            // it's almost Haskell <3
        }
    }
}

// returns true iff wff b can be obtained from wff a by applying
// the substitution subst *zero or more* times.
fn substitution_applied_wff_zero_or_more_times(a: &Wff, b: &Wff, subst: (&Term, &Term)) -> bool {
    match (&a, &b) {
        (Wff::And(conjs1), Wff::And(conjs2)) => zip(conjs1, conjs2)
            .all(|(c1, c2)| substitution_applied_wff_zero_or_more_times(c1, c2, subst)),
        (Wff::And(_), _) => false,

        (Wff::Or(disjs1), Wff::Or(disjs2)) => zip(disjs1, disjs2)
            .all(|(d1, d2)| substitution_applied_wff_zero_or_more_times(d1, d2, subst)),
        (Wff::Or(_), _) => false,

        (Wff::Implies(ante1, conseq1), Wff::Implies(ante2, conseq2)) => {
            substitution_applied_wff_zero_or_more_times(ante1, ante2, subst)
                && substitution_applied_wff_zero_or_more_times(conseq1, conseq2, subst)
        }
        (Wff::Implies(..), _) => false,

        (Wff::Bicond(w11, w12), Wff::Bicond(w21, w22)) => {
            substitution_applied_wff_zero_or_more_times(w11, w21, subst)
                && substitution_applied_wff_zero_or_more_times(w12, w22, subst)
        }
        (Wff::Bicond(..), _) => false,

        (Wff::Not(w1), Wff::Not(w2)) => substitution_applied_wff_zero_or_more_times(w1, w2, subst),
        (Wff::Not(..), _) => false,

        (Wff::Bottom, Wff::Bottom) => true,
        (Wff::Bottom, _) => false,

        (Wff::Equals(t11, t12), Wff::Equals(t21, t22)) => {
            substitution_applied_term_zero_or_more_times(t11, t21, subst)
                && substitution_applied_term_zero_or_more_times(t12, t22, subst)
        }
        (Wff::Equals(..), _) => false,

        (Wff::Atomic(_), Wff::Atomic(_)) => a == b,
        (Wff::Atomic(_), _) => false,

        (Wff::PredApp(p1, args1), Wff::PredApp(p2, args2)) => {
            p1 == p2
                && args1.len() == args2.len()
                && zip(args1, args2)
                    .all(|(t1, t2)| substitution_applied_term_zero_or_more_times(t1, t2, subst))
        }
        (Wff::PredApp(..), _) => false,

        (Wff::Forall(var1, wff1), Wff::Forall(var2, wff2)) => {
            var1 == var2 && substitution_applied_wff_zero_or_more_times(wff1, wff2, subst)
        }
        (Wff::Forall(..), _) => false,

        (Wff::Exists(var1, wff1), Wff::Exists(var2, wff2)) => {
            var1 == var2 && substitution_applied_wff_zero_or_more_times(wff1, wff2, subst)
        }
        (Wff::Exists(..), _) => false,
    }
}

// returns true iff wff b can be obtained from wff a by applying
// the substitution subst *one or more* times.
fn substitution_applied_wff_one_or_more_times(a: &Wff, b: &Wff, subst: (&Term, &Term)) -> bool {
    (a != b && substitution_applied_wff_zero_or_more_times(a, b, subst))
        || (a == b && subst.0 == subst.1 && wff_contains_term(a, subst.0))
}

// returns true iff term a contains term b at least once (or term a and b are syntactically equal)
fn term_contains_term(a: &Term, b: &Term) -> bool {
    match &a {
        Term::Atomic(_) => a == b,
        Term::FuncApp(_, args) => a == b || args.iter().any(|arg| term_contains_term(arg, b)),
    }
}

// returns true iff wff a contains term b at least once
fn wff_contains_term(a: &Wff, b: &Term) -> bool {
    match &a {
        Wff::Bottom | Wff::Atomic(_) => false,
        Wff::Or(li) | Wff::And(li) => li.iter().any(|l| wff_contains_term(l, b)),
        Wff::Not(w) => wff_contains_term(w, b),
        Wff::Implies(w1, w2) | Wff::Bicond(w1, w2) => {
            wff_contains_term(w1, b) || wff_contains_term(w2, b)
        }
        Wff::Equals(t1, t2) => term_contains_term(t1, b) || term_contains_term(t2, b),
        Wff::Forall(_, w) | Wff::Exists(_, w) => wff_contains_term(w, b),
        Wff::PredApp(_, args) => args.iter().any(|arg| term_contains_term(arg, b)),
    }
}

// applies a substitution everywhere and returns the resulting wff.
// Note that this substitution must be trivial: that is, the substitution
// must be of the form <term1> -> <term2> where <term1> is an atomic term,
// i.e. a constant or variable, so not a function application.
fn apply_trivial_substitution_everywhere_to_wff(wff: &Wff, subst: (&Term, &Term)) -> Wff {
    match subst.0 {
        Term::FuncApp(..) => panic!("Substitution is not trivial"),
        Term::Atomic(_) => {}
    }

    // applies a substitution everywhere and returns the resulting term.
    // Note that this substitution must be trivial: that is, the substitution
    // must be of the form <term1> -> <term2> where <term1> is an atomic term,
    // i.e. a constant or variable, so not a function application.
    fn apply_trivial_substitution_everywhere_to_term(term: &Term, subst: (&Term, &Term)) -> Term {
        match subst.0 {
            Term::FuncApp(..) => panic!("Substitution is not trivial"),
            Term::Atomic(_) => {}
        }

        match term {
            Term::FuncApp(f, args) => Term::FuncApp(
                f.to_string(),
                args.iter()
                    .map(|arg| apply_trivial_substitution_everywhere_to_term(arg, subst))
                    .collect(),
            ),
            Term::Atomic(_) if term == subst.0 => subst.1.clone(),
            Term::Atomic(_) => term.clone(),
        }
    }

    match wff {
        Wff::And(li) => Wff::And(
            li.iter().map(|x| apply_trivial_substitution_everywhere_to_wff(x, subst)).collect(),
        ),
        Wff::Or(li) => Wff::Or(
            li.iter().map(|x| apply_trivial_substitution_everywhere_to_wff(x, subst)).collect(),
        ),
        Wff::Implies(w1, w2) => Wff::Implies(
            Box::new(apply_trivial_substitution_everywhere_to_wff(w1, subst)),
            Box::new(apply_trivial_substitution_everywhere_to_wff(w2, subst)),
        ),
        Wff::Bicond(w1, w2) => Wff::Bicond(
            Box::new(apply_trivial_substitution_everywhere_to_wff(w1, subst)),
            Box::new(apply_trivial_substitution_everywhere_to_wff(w2, subst)),
        ),
        Wff::Not(w1) => Wff::Not(Box::new(apply_trivial_substitution_everywhere_to_wff(w1, subst))),
        Wff::Bottom => Wff::Bottom,
        Wff::Forall(s, w) => Wff::Forall(
            s.to_string(),
            Box::new(apply_trivial_substitution_everywhere_to_wff(w, subst)),
        ),
        Wff::Exists(s, w) => Wff::Exists(
            s.to_string(),
            Box::new(apply_trivial_substitution_everywhere_to_wff(w, subst)),
        ),
        Wff::Equals(t1, t2) => Wff::Equals(
            apply_trivial_substitution_everywhere_to_term(t1, subst),
            apply_trivial_substitution_everywhere_to_term(t2, subst),
        ),
        Wff::PredApp(p, li) => Wff::PredApp(
            p.to_string(),
            li.iter().map(|x| apply_trivial_substitution_everywhere_to_term(x, subst)).collect(),
        ),
        Wff::Atomic(p) => Wff::Atomic(p.to_string()),
    }
}

// given two wffs, wff1 and wff2, this function tries to determine if there exists a *trivial*
// substitution of the form A -> B where A is not equal to B such that wff2 can be
// obtained from wff1 only by applying that substitution at
// least one time. If such a substitution exists, then this function returns it. If such a
// substitution does not exist, then the return value of this function is undefined! So, if this
// function returns some substitution, you should always check it yourself that it is actually
// possible to obtain wff2 from wff1 by only applying the substitution. If this function returns
// None, then you know for sure that there exists no trivial substitution that can convert wff1
// into wff2 by applying it at least once.
fn find_possible_trivial_substitution_wff(wff1: &Wff, wff2: &Wff) -> Option<(Term, Term)> {
    fn find_possible_trivial_substitution_term(term1: &Term, term2: &Term) -> Option<(Term, Term)> {
        if term1 == term2 {
            None
        } else if let Term::Atomic(..) = term1 {
            Some((term1.clone(), term2.clone()))
        } else if let (Term::FuncApp(_, args1), Term::FuncApp(_, args2)) = (term1, term2) {
            zip(args1, args2).find_map(|(a1, a2)| find_possible_trivial_substitution_term(a1, a2))
        } else {
            None
        }
    }
    match (wff1, wff2) {
        (Wff::And(li1), Wff::And(li2)) => {
            zip(li1, li2).find_map(|(w1, w2)| find_possible_trivial_substitution_wff(w1, w2))
        }
        (Wff::And(_), _) => None,

        (Wff::Or(li1), Wff::Or(li2)) => {
            zip(li1, li2).find_map(|(w1, w2)| find_possible_trivial_substitution_wff(w1, w2))
        }
        (Wff::Or(_), _) => None,

        (Wff::Implies(a1, c1), Wff::Implies(a2, c2)) => {
            find_possible_trivial_substitution_wff(a1, a2)
                .or(find_possible_trivial_substitution_wff(c1, c2))
        }
        (Wff::Implies(..), _) => None,

        (Wff::Bicond(w11, w12), Wff::Bicond(w21, w22)) => {
            find_possible_trivial_substitution_wff(w11, w21)
                .or(find_possible_trivial_substitution_wff(w12, w22))
        }
        (Wff::Bicond(..), _) => None,

        (Wff::Not(w1), Wff::Not(w2)) => find_possible_trivial_substitution_wff(w1, w2),
        (Wff::Not(..), _) => None,

        (Wff::Forall(_, w1), Wff::Forall(_, w2)) => find_possible_trivial_substitution_wff(w1, w2),
        (Wff::Forall(..), _) => None,

        (Wff::Exists(_, w1), Wff::Exists(_, w2)) => find_possible_trivial_substitution_wff(w1, w2),
        (Wff::Exists(..), _) => None,

        (Wff::Atomic(_), _) => None,

        (Wff::PredApp(_, args1), Wff::PredApp(_, args2)) => {
            zip(args1, args2).find_map(|(a1, a2)| find_possible_trivial_substitution_term(a1, a2))
        }
        (Wff::PredApp(..), _) => None,

        (Wff::Equals(t11, t12), Wff::Equals(t21, t22)) => {
            find_possible_trivial_substitution_term(t11, t21)
                .or(find_possible_trivial_substitution_term(t12, t22))
        }
        (Wff::Equals(..), _) => None,

        (Wff::Bottom, _) => None,
    }
}
