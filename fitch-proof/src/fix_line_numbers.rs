use crate::data::*;
use std::collections::HashMap;

/// This function 'fixes' the line numbers in a vector of [ProofLine]s.
///
/// If the line numbers already start at 1 and increase by one at a time, then this function does
/// nothing. However, this function does do something in case the line numbers are not properly
/// starting at 1 and increasing by one at a time. This function modifies the [ProofLine]s such
/// that the line numbers will start at 1 and increase by one at a time.
///
/// This function also updates the justifications with the new line numbers, so those do not get
/// messed up. This can be very useful if you have a big proof and you want to delete one unused
/// line in the middle, or if you want to insert a line in the middle. If you want to insert a line
/// in the middle of a big proof, just give that line the line number 1000 (or any unused value)
/// and then apply this function. It will fix all the line numbers and justifications.
///
/// If the proof contains justifications which have line numbers that do not exist in the proof,
/// these line numbers will be set to zero in the justification.
pub fn fix_line_numbers(proof_lines: &mut [ProofLine]) {
    let mut line_num_map: HashMap<usize, usize> = HashMap::from([]);
    let mut last_line_num: usize = 0;
    for line in &mut *proof_lines {
        if line.line_num.is_some() {
            line_num_map.insert(line.line_num.unwrap(), last_line_num + 1);
            last_line_num += 1;
            line.line_num = Some(last_line_num);
        }
    }

    let new_val = |x: &usize| *line_num_map.get(x).unwrap_or(&0);

    for line in &mut *proof_lines {
        if line.justification.is_some() {
            line.justification = Some(match line.justification.as_ref().unwrap() {
                Justification::Reit(n) => Justification::Reit(new_val(n)),
                Justification::AndIntro(ns) => {
                    Justification::AndIntro(ns.iter().map(new_val).collect())
                }
                Justification::AndElim(n) => Justification::AndElim(new_val(n)),
                Justification::OrIntro(n) => Justification::OrIntro(new_val(n)),
                Justification::OrElim(n, subs) => Justification::OrElim(
                    new_val(n),
                    subs.iter().map(|(a, b)| (new_val(a), new_val(b))).collect(),
                ),
                Justification::EqualsIntro => Justification::EqualsIntro,
                Justification::EqualsElim(n, m) => {
                    Justification::EqualsElim(new_val(n), new_val(m))
                }
                Justification::NotIntro((n, m)) => {
                    Justification::NotIntro((new_val(n), new_val(m)))
                }
                Justification::NotElim(n) => Justification::NotElim(new_val(n)),
                Justification::BottomIntro(n, m) => {
                    Justification::BottomIntro(new_val(n), new_val(m))
                }
                Justification::BottomElim(n) => Justification::BottomElim(new_val(n)),
                Justification::BicondIntro((a, b), (c, d)) => {
                    Justification::BicondIntro((new_val(a), new_val(b)), (new_val(c), new_val(d)))
                }
                Justification::BicondElim(n, m) => {
                    Justification::BicondElim(new_val(n), new_val(m))
                }
                Justification::ForallIntro((a, b)) => {
                    Justification::ForallIntro((new_val(a), new_val(b)))
                }
                Justification::ForallElim(n) => Justification::ForallElim(new_val(n)),
                Justification::ExistsIntro(n) => Justification::ExistsIntro(new_val(n)),
                Justification::ExistsElim(n, (a, b)) => {
                    Justification::ExistsElim(new_val(n), (new_val(a), new_val(b)))
                }
                Justification::ImpliesIntro((n, m)) => {
                    Justification::ImpliesIntro((new_val(n), new_val(m)))
                }
                Justification::ImpliesElim(n, m) => {
                    Justification::ImpliesElim(new_val(n), new_val(m))
                }
            });
        }
    }
}
