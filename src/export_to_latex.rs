use crate::data::*;
use crate::formatter::format_wff;
use std::fmt::Write;

pub fn proof_to_latex(proof: &[ProofLine]) -> String {
    let mut prev_depth = 1;
    let proof_str = proof.iter().fold(String::new(), |mut output, l| {
        if l.line_num.is_none() {
            return output;
        }
        let part1 = if l.depth == prev_depth + 1 {
            prev_depth += 1;
            "\\open\n"
        } else if l.depth == prev_depth - 1 {
            prev_depth -= 1;
            "\\close\n"
        } else {
            ""
        };
        let part2 = format!(
            "{}{{{}}}{{{}{}}}", // this is your fate if you write a latex exporter
            if l.justification.is_none() {
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
                Some(wff) => sentence_to_latex(wff),
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

fn sentence_to_latex(wff: &Wff) -> String {
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
