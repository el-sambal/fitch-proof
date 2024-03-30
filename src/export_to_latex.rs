use crate::data::*;
use crate::proof::*;

pub fn proof_to_latex(proof: &Proof) -> String {
    let mut prev_depth = 1;
    let proof_str = proof
        .lines
        .iter()
        .map(|l| {
            let part1 = if l.line_num == Some(prev_depth + 1) {
                prev_depth += 1;
                "\\open\n"
            } else if l.line_num == Some(prev_depth - 1) {
                prev_depth -= 1;
                "\\close\n"
            } else {
                ""
            };
            let part2 = match &l.sentence {
                Some(wff) => sentence_to_latex(wff),
                _ => "".to_string(),
            };
            let part3 = match &l.sentence {
                Some(wff) => sentence_to_latex(wff),
                _ => "".to_string(),
            };
            format!("{}{}{}\n", part1, part2, part3)
        })
        .collect::<String>();
    format!("{}{}{}", "$\\begin{nd}", proof_str, "\\end{nd}$")
}

/* ------------------ PRIVATE -------------------- */

fn sentence_to_latex(wff: &Wff) -> String {
    todo!()
}
