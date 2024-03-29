use std::iter::zip;

use crate::data::*;

// Formats a proof.
//
// PRECONDITION (panics otherwise): !proof_lines.is_empty()
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

    line_strings.join("\n")
}

/* ------------------ PRIVATE -------------------- */

// Given a slice of Strings, this function modifies it by padding all strings with spaces so
// as to be equally long as the longest String found in the slice, plus `extra` number of spaces.
// After calling this function, all strings in the slice have the same length.
fn pad_to_same_length(strings: &mut [String], extra: usize) {
    let longest_line_length = strings.iter().map(|x| x.chars().count()).max().unwrap();
    for string in &mut *strings {
        let pad_width = extra + longest_line_length - string.chars().count();
        string.push_str(&" ".repeat(pad_width));
    }
}

fn format_term(term: &Term) -> String {
    match term {
        Term::Atomic(t) => t.to_owned(),
        Term::FuncApp(f, args) => {
            format!("{}({})", f, args.iter().map(format_term).collect::<Vec<_>>().join(","))
        }
    }
}

fn format_wff(wff: &Wff) -> String {
    match wff {
        Wff::Bottom => "⊥".to_owned(),
        Wff::Or(li) => format!("({})", li.iter().map(format_wff).collect::<Vec<_>>().join(" ∨ ")),
        Wff::And(li) => format!("({})", li.iter().map(format_wff).collect::<Vec<_>>().join(" ∧ ")),
        Wff::Not(w) => format!("¬{}", format_wff(w)),
        Wff::Implies(w1, w2) => format!("({} → {})", format_wff(w1), format_wff(w2)),
        Wff::Bicond(w1, w2) => format!("({} ↔ {})", format_wff(w1), format_wff(w2)),
        Wff::Forall(s, w) => format!("∀{} {}", s, format_wff(w)),
        Wff::Exists(s, w) => format!("∃{} {}", s, format_wff(w)),
        Wff::PredApp(s, args) => {
            format!("{}({})", s, args.iter().map(format_term).collect::<Vec<_>>().join(","))
        }
        Wff::Atomic(p) => p.to_string(),
        Wff::Equals(t1, t2) => format!("{}={}", format_term(t1), format_term(t2)),
    }
}
