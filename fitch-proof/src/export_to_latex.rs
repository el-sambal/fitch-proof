use crate::data::*;
use crate::formatter::format_wff;
use std::fmt::Write;

/// Exports a proof to a string that can be put in a LaTeX document.
pub fn proof_to_latex(proof: &[ProofLine]) -> String {
    let mut prev_depth = 1;
    let mut is_hypo = true;
    let proof_str = proof.iter().fold(String::new(), |mut output, l| {
        if l.is_fitch_bar_line {
            is_hypo = false;
        }
        let part1 = if l.depth == prev_depth + 1 {
            prev_depth += 1;
            is_hypo = true;
            "\\open\n"
        } else if l.depth == prev_depth - 1 {
            prev_depth -= 1;
            "\\close\n"
        } else {
            ""
        };
        if l.line_num.is_none() {
            let _ = write!(output, "{}", part1);
            return output;
        }
        let part2 = format!(
            "{}{{{}}}{{{}{}}}",
            if is_hypo {
                "\\hypo"
            } else {
                "\\have"
            },
            l.line_num.unwrap(),
            match &l.constant_between_square_brackets {
                Some(Term::Atomic(t)) => format!(" \\boxed{{{}}}~ ", t),
                _ => "".to_string(),
            },
            match &l.sentence {
                Some(wff) => wff_to_latex(wff),
                _ => "".to_string(),
            },
        );
        let part3 = match &l.justification {
            Some(just) => justification_to_latex(just),
            _ => "".to_string(),
        };
        let _ = writeln!(output, "{}{}{}", part1, part2, part3);
        output
    });
    format!("{}{}{}", "$\n\\begin{nd}\n", proof_str, "\\end{nd}\n$")
        .replace("  ", " ")
        .replace("{ ", "{")
        .replace(" }", "}")
        .replace(" \\", "\\")
}

/* ------------------ PRIVATE -------------------- */

/// Converts a [Wff] to a LaTeX string. This uses [format_wff] under the hood.
fn wff_to_latex(wff: &Wff) -> String {
    let formatted = format_wff(wff);

    // better too many spaces then not enough...
    // we will eliminate duplicate spaces later
    formatted
        .replace('∧', " \\land ")
        .replace('∨', " \\lor ")
        .replace('¬', " \\neg ")
        .replace('→', " \\rightarrow ")
        .replace('↔', " \\leftrightarrow ")
        .replace('⊥', " \\bot ")
        .replace('∀', "\\forall ")
        .replace('∃', "\\exists ")
}

/// Converts a [Justification] to a LaTeX string.
fn justification_to_latex(just: &Justification) -> String {
    match just {
        Justification::Reit(n) => format!("\\r{{{n}}}"),
        Justification::AndIntro(ns) => {
            format!(
                "\\ai{{{}}}",
                ns.iter().map(|n| n.to_string()).collect::<Vec<String>>().join(",")
            )
        }
        Justification::AndElim(n) => format!("\\ae{{{n}}}"),
        Justification::OrIntro(n) => format!("\\oi{{{n}}}"),
        Justification::OrElim(n, subs) => format!(
            "\\oe{{{},{}}}",
            n,
            subs.iter().map(|(a, b)| format!("{}-{}", a, b)).collect::<Vec<String>>().join(",")
        ),
        Justification::NotIntro((a, b)) => format!("\\ni{{{a}-{b}}}"),
        Justification::NotElim(n) => format!("\\ne{{{n}}}"),
        Justification::EqualsIntro => "\\idi".to_owned(),
        Justification::EqualsElim(n, m) => format!("\\ide{{{n},{m}}}"),
        Justification::ImpliesIntro((n, m)) => format!("\\ii{{{n}-{m}}}"),
        Justification::ImpliesElim(n, m) => format!("\\ie{{{n},{m}}}"),
        Justification::BicondIntro((a, b), (c, d)) => format!("\\bci{{{a}-{b},{c}-{d}}}"),
        Justification::BicondElim(n, m) => format!("\\bce{{{n},{m}}}"),
        Justification::BottomIntro(n, m) => format!("\\bi{{{n},{m}}}"),
        Justification::BottomElim(n) => format!("\\be{{{n}}}"),
        Justification::ForallIntro((a, b)) => format!("\\Ai{{{a}-{b}}}"),
        Justification::ForallElim(n) => format!("\\Ae{{{n}}}"),
        Justification::ExistsIntro(n) => format!("\\Ei{{{n}}}"),
        Justification::ExistsElim(n, (a, b)) => format!("\\Ee{{{n},{a}-{b}}}"),
    }
}
