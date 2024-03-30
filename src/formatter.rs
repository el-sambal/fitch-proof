use std::iter::zip;

use crate::data::*;

/// Formats a proof.
///
/// PRECONDITION (panics otherwise): !proof_lines.is_empty()
pub fn format_proof(proof_lines: Vec<ProofLine>) -> String {
    // here we build the formatted proof
    let mut line_strings: Vec<String> = proof_lines
        .iter()
        .map(|pl| {
            if pl.line_num.is_some() {
                pl.line_num.unwrap().to_string()
            } else {
                "".to_string()
            }
        })
        .collect();

    pad_to_same_length(&mut line_strings, 1);

    for (line, line_string) in zip(&proof_lines, &mut line_strings) {
        line_string.push_str(&"| ".repeat(line.depth));
    }

    for (line, line_string) in zip(&proof_lines, &mut line_strings) {
        if line.is_fitch_bar_line {
            line_string.push_str(" ---");
        }
    }

    for (line, line_string) in zip(&proof_lines, &mut line_strings) {
        if line.constant_between_square_brackets.is_some() {
            line_string.push('[');
            line_string.push_str(match line.constant_between_square_brackets.as_ref().unwrap() {
                Term::Atomic(str) => str,
                _ => panic!(),
            });
            line_string.push_str("] ");
        }
    }

    for (line, line_string) in zip(&proof_lines, &mut line_strings) {
        if line.sentence.is_some() {
            line_string.push_str(&format_wff(line.sentence.as_ref().unwrap()));
        }
    }

    pad_to_same_length(&mut line_strings, 9);

    for (line, line_string) in zip(&proof_lines, &mut line_strings) {
        if line.justification.is_some() {
            line_string.push_str(&format_justification(line.justification.as_ref().unwrap()));
        }
    }

    for line_string in &mut line_strings {
        remove_whitespace_at_end( line_string);
    }

    line_strings.join("\n")
}

/* ------------------ PRIVATE -------------------- */

/// Given a slice of [String]s, this function modifies it by padding all strings with spaces so
/// as to be equally long as the longest [String] found in the slice, plus `extra` number of spaces.
/// After calling this function, all strings in the slice have the same length.
fn pad_to_same_length(strings: &mut [String], extra: usize) {
    let longest_line_length = strings.iter().map(|x| x.chars().count()).max().unwrap();
    for string in &mut *strings {
        let pad_width = extra + longest_line_length - string.chars().count();
        string.push_str(&" ".repeat(pad_width));
    }
}

/// Formats a [Term].
fn format_term(term: &Term) -> String {
    match term {
        Term::Atomic(t) => t.to_owned(),
        Term::FuncApp(f, args) => {
            format!("{}({})", f, args.iter().map(format_term).collect::<Vec<_>>().join(","))
        }
    }
}

/// Formats a [Wff].
fn format_wff(wff: &Wff) -> String {
    fn wff_with_brackets(wff: &Wff) -> String {
        match wff {
            Wff::Bottom => "⊥".to_owned(),
            Wff::Or(li) => {
                format!("({})", li.iter().map(wff_with_brackets).collect::<Vec<_>>().join(" ∨ "))
            }
            Wff::And(li) => {
                format!("({})", li.iter().map(wff_with_brackets).collect::<Vec<_>>().join(" ∧ "))
            }
            Wff::Not(w) => format!("¬{}", wff_with_brackets(w)),
            Wff::Implies(w1, w2) => {
                format!("({} → {})", wff_with_brackets(w1), wff_with_brackets(w2))
            }
            Wff::Bicond(w1, w2) => {
                format!("({} ↔ {})", wff_with_brackets(w1), wff_with_brackets(w2))
            }
            Wff::Forall(s, w) => format!("∀{} {}", s, wff_with_brackets(w)),
            Wff::Exists(s, w) => format!("∃{} {}", s, wff_with_brackets(w)),
            Wff::PredApp(s, args) => {
                format!("{}({})", s, args.iter().map(format_term).collect::<Vec<_>>().join(","))
            }
            Wff::Atomic(p) => p.to_string(),
            Wff::Equals(t1, t2) => format!("({}={})", format_term(t1), format_term(t2)),
        }
    }
    let wff_string = wff_with_brackets(wff);

    // now we have a wff, but it will have outermost brackets in case the top level 'connective' was
    // and, or, implies, bicond or equals. So we will have to remove those.

    match wff {
        Wff::And(..) | Wff::Or(..) | Wff::Implies(..) | Wff::Bicond(..) | Wff::Equals(..) => {
            let mut it = wff_string.chars();
            it.next();
            it.next_back();
            it.as_str().to_string()
        }
        _ => wff_string,
    }
}

/// Makes a [String] out of a [Justification].
fn format_justification(just: &Justification) -> String {
    match just {
        Justification::Reit(n) => format!("Reit: {n}"),
        Justification::AndIntro(ns) => {
            format!("∧ Intro: {}", ns.iter().map(|n| n.to_string()).collect::<Vec<_>>().join(", "))
        }
        Justification::AndElim(n) => format!("∧ Elim: {n}"),
        Justification::OrIntro(n) => format!("∨ Intro: {n}"),
        Justification::OrElim(n, subs) => format!(
            "∨ Elim: {n}, {}",
            subs.iter().map(|(a, b)| format!("{a}-{b}")).collect::<Vec<_>>().join(", ")
        ),
        Justification::ImpliesIntro((a, b)) => format!("→ Intro: {a}-{b}"),
        Justification::ImpliesElim(n, m) => format!("→ Elim: {n},{m}"),
        Justification::BicondIntro((a, b), (c, d)) => format!("↔ Intro: {a}-{b}, {c}-{d}"),
        Justification::BicondElim(n, m) => format!("↔ Elim: {n}, {m}"),
        Justification::EqualsIntro => "= Intro".to_owned(),
        Justification::EqualsElim(n, m) => format!("= Elim: {n}, {m}"),
        Justification::NotElim(n) => format!("¬ Elim: {n}"),
        Justification::NotIntro((a, b)) => format!("¬ Intro: {a}-{b}"),
        Justification::BottomElim(n) => format!("⊥ Elim: {n}"),
        Justification::BottomIntro(n, m) => format!("⊥ Intro: {n}, {m}"),
        Justification::ForallIntro((a, b)) => format!("∀ Intro: {a}-{b}"),
        Justification::ForallElim(n) => format!("∀ Elim: {n}"),
        Justification::ExistsIntro(n) => format!("∃ Intro: {n}"),
        Justification::ExistsElim(n, (a, b)) => format!("∃ Elim: {n}, {a}-{b}"),
    }
}

/// This function removes any spaces at the end of a [String].
fn remove_whitespace_at_end(s: &mut String) {
    let rpo = s.chars().collect::<Vec<_>>().iter().rposition(|c| c != &' ').unwrap();
    *s=s.chars().take(rpo+1).collect::<String>();
}
