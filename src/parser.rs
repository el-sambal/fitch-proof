use std::iter;
use std::iter::from_fn;

use crate::data::*;

pub fn parse_logical_expression_string(expr: &str) -> Option<Wff> {
    if let Ok(toks) = lex_logical_expr(expr) {
        return parse_logical_expr(&toks);
    }
    None
}

pub fn parse_fitch_proof(proof: &str) -> Result<Vec<ProofLine>, String> {
    let mut last_line_num = 0;
    proof
        .lines()
        .filter(|s| !s.is_empty())
        .map(|x| {
            if let Ok(toks) = lex_logical_expr(x) {
                if let Some(line) = parse_proof_line(&toks) {
                    if let Some(line_num) = line.line_num {
                        last_line_num = line_num;
                    }
                    Ok(line)
                } else {
                    Err(format!(
                        "Parser failure somewhere after line {last_line_num}."
                    ))
                }
            } else {
                Err(format!(
                    "Lexer failure somewhere after line {last_line_num}. \
                    You are most likely using an illegal character."
                ))
            }
        })
        .collect()
}

/* ----------------- PRIVATE -------------------*/

#[derive(PartialEq, Debug)]
enum Token {
    Name(String),
    LPar,
    RPar,
    Forall,
    Exists,
    And,
    Or,
    Implies,
    Not,
    Bot,
    Comma,
    Equals,
    Number(usize),
    ConseqVertBar(usize),
    Colon,
    Dash,
    LSqBracket,
    RSqBracket,
}

fn lex_logical_expr(input: &str) -> Result<Vec<Token>, String> {
    let mut toks: Vec<Token> = Vec::new();
    let mut input_iter = input.chars().peekable();

    while let Some(ch) = input_iter.next() {
        match ch {
            ' ' => {} // ignore spaces
            '(' => toks.push(Token::LPar),
            ')' => toks.push(Token::RPar),
            '\u{2200}' => toks.push(Token::Forall),
            '\u{2203}' => toks.push(Token::Exists),
            '\u{2227}' => toks.push(Token::And),
            '\u{2228}' => toks.push(Token::Or),
            '\u{2192}' => toks.push(Token::Implies),
            '\u{00AC}' => toks.push(Token::Not),
            ',' => toks.push(Token::Comma),
            '=' => toks.push(Token::Equals),
            'a'..='z' | 'A'..='Z' => {
                let name = iter::once(ch)
                    .chain(from_fn(|| {
                        input_iter.by_ref().next_if(|c| c.is_ascii_alphabetic())
                    }))
                    .collect::<String>();
                toks.push(Token::Name(name));
            }
            '1'..='9' => {
                let num: usize = iter::once(ch)
                    .chain(from_fn(|| {
                        input_iter.by_ref().next_if(|c| c.is_ascii_digit())
                    }))
                    .collect::<String>()
                    .parse()
                    .unwrap();
                toks.push(Token::Number(num));
            }
            '|' => {
                let num: usize = iter::once(ch)
                    .chain(from_fn(|| {
                        input_iter.by_ref().next_if(|c| c == &'|' || c == &' ')
                    }))
                    .filter(|c| c == &'|')
                    .collect::<String>()
                    .len();
                toks.push(Token::ConseqVertBar(num));
            }
            ':' => toks.push(Token::Colon),
            '-' => toks.push(Token::Dash),
            '[' => toks.push(Token::LSqBracket),
            ']' => toks.push(Token::RSqBracket),
            '⊥' => toks.push(Token::Bot),
            _ => {
                let mut err: String = "invalid character found: ".to_owned();
                err.push_str(&ch.to_string());
                return Err(err);
            }
        }
    }

    Ok(toks)
}

// The grammar: (brackets denote tokens; {} is EBNF notation for 0 or more times)
//
// <E1> ::=
//            <E2>
//          | <E2> and <E2> {and <E2>}
//          | <E2> or <E2> {or <E2>}
//          | <E2> implies <E2>
//
// <E2> ::=
//            <E3>
//          | <Term> equals <Term>
//
// <E3> ::=
//            <PredicateName> <ArgList>
//          | <AtomicPropositionName>
//          | ( <E1> )
//          | forall <VariableOrConstantName> <E3>
//          | exists <VariableOrConstantName> <E3>
//          | not <E3>
//
// <Term> ::=
//              <FunctionName> <ArgList>
//            | <VariableOrConstantName>
//
// <ArgList> ::= ( <Term> {, <Term>} )
//
// <FunctionName> : some string starting with a lowercase letter
// <VariableOrConstantName> : some string starting with a lowercase letter
// <PredicateName> : some string starting with an UPPERCASE letter
// <AtomicPropositionName> : some string starting with an UPPERCASE letter

fn parse_logical_expr(toks: &[Token]) -> Option<Wff> {
    if let Some((wff, rem_toks)) = parse_e1(toks) {
        if rem_toks.is_empty() {
            // there should be no remaining tokens!
            return Some(wff);
        } else {
            return None;
        }
    }
    None
}

fn parse_e1(toks: &[Token]) -> Option<(Wff, &[Token])> {
    // always accept the first <E2>
    if let Some((wff, mut rem_toks)) = parse_e2(toks) {
        if rem_toks.is_empty() {
            return Some((wff, rem_toks));
        }
        return match rem_toks[0] {
            // <E2> implies <E2>
            Token::Implies => {
                if let Some((wff2, rem_rem_toks)) = parse_e2(rem_toks.get(1..)?) {
                    return Some((Wff::Implies(Box::new(wff), Box::new(wff2)), rem_rem_toks));
                }
                None
            }
            // <E2> and <E2> {and <E2>}
            Token::And => {
                let mut conjs: Vec<Wff> = vec![wff];
                while !rem_toks.is_empty() && rem_toks[0] == Token::And {
                    if let Some((new_wff, rem_rem_toks)) = parse_e2(rem_toks.get(1..)?) {
                        rem_toks = rem_rem_toks;
                        conjs.push(new_wff);
                    } else {
                        return None;
                    }
                }
                Some((Wff::And(conjs), rem_toks))
            }
            // <E2> or <E2> {or <E2>}
            Token::Or => {
                let mut disjs: Vec<Wff> = vec![wff];
                while !rem_toks.is_empty() && rem_toks[0] == Token::Or {
                    if let Some((new_wff, rem_rem_toks)) = parse_e2(rem_toks.get(1..)?) {
                        rem_toks = rem_rem_toks;
                        disjs.push(new_wff);
                    } else {
                        return None;
                    }
                }
                Some((Wff::Or(disjs), rem_toks))
            }
            // found just a single <E2>
            _ => Some((wff, rem_toks)),
        };
    }

    None
}

fn parse_e2(toks: &[Token]) -> Option<(Wff, &[Token])> {
    // just <E3>
    if let Some((wff, rem_toks)) = parse_e3(toks) {
        return Some((wff, rem_toks));
    }

    // <Term> equals <Term>
    if let Some((term1, rem_toks1)) = parse_term(toks) {
        if rem_toks1.first()? == &Token::Equals {
            if let Some((term2, rem_toks2)) = parse_term(rem_toks1.get(1..)?) {
                return Some((Wff::Equals(term1, term2), rem_toks2));
            }
        }
    }

    None
}

fn parse_e3(toks: &[Token]) -> Option<(Wff, &[Token])> {
    match toks.first()? {
        Token::Name(name) if name.chars().next()?.is_uppercase() => {
            if let Some((terms, rem_toks)) = parse_arg_list(toks.get(1..)?) {
                Some((Wff::PredApp(name.to_string(), terms), rem_toks))
            } else {
                Some((Wff::Atomic(name.to_string()), &toks[1..]))
            }
        }
        Token::Not => {
            if let Some((wff, rem_toks)) = parse_e3(&toks[1..]) {
                Some((Wff::Not(Box::new(wff)), rem_toks))
            } else {
                None
            }
        }
        Token::LPar => {
            if let Some((wff, rem_toks)) = parse_e1(&toks[1..]) {
                if rem_toks.first()? == &Token::RPar {
                    return Some((wff, &rem_toks[1..]));
                }
            }
            None
        }
        Token::Forall => match toks.get(1)? {
            Token::Name(name) if name.chars().next()?.is_lowercase() => {
                if let Some((wff, rem_toks)) = parse_e3(toks.get(2..)?) {
                    return Some((Wff::Forall(name.to_owned(), Box::new(wff)), rem_toks));
                }
                None
            }
            _ => None,
        },
        Token::Exists => match toks.get(1)? {
            Token::Name(name) if name.chars().next()?.is_lowercase() => {
                if let Some((wff, rem_toks)) = parse_e3(toks.get(2..)?) {
                    return Some((Wff::Exists(name.to_owned(), Box::new(wff)), rem_toks));
                }
                None
            }
            _ => None,
        },
        _ => None,
    }
}

fn parse_term(toks: &[Token]) -> Option<(Term, &[Token])> {
    match toks.first()? {
        Token::Name(name) => {
            if let Some((terms, rem_toks)) = parse_arg_list(&toks[1..]) {
                Some((Term::FuncApp(name.to_string(), terms), rem_toks))
            } else {
                Some((Term::Atomic(name.to_string()), &toks[1..]))
            }
        }
        _ => None,
    }
}

fn parse_arg_list(toks: &[Token]) -> Option<(Vec<Term>, &[Token])> {
    if toks.first()? != &Token::LPar {
        return None;
    }

    let mut terms: Vec<Term> = vec![];

    if let Some((term, mut rem_toks)) = parse_term(&toks[1..]) {
        terms.push(term);
        while rem_toks.first()? == &Token::Comma {
            if let Some((term2, rem_rem_toks)) = parse_term(rem_toks.get(1..)?) {
                terms.push(term2);
                rem_toks = rem_rem_toks;
            }
        }

        if rem_toks.first()? == &Token::RPar {
            Some((terms, &rem_toks[1..]))
        } else {
            None
        }
    } else {
        None
    }
}

// The grammar of a Fitch proof:
//
// <FitchProof> is several <FitchProofLine>s separated by newline
// <FitchProofLine> ::=
//                        <num> '|' { '|' } <E1> <Justification>             // non-premise
//                      | <num> '|' { '|' } <E1>                             // premise
//                      | <num> '|' { '|' } '[' <ConstantName> ']' [ <E1> ]  // premise with box
//                      | '|' { '|' } - { - }                                // fitch bar
//                      | '|' { '|' }                                        // empty line
//
// <ConstantName> : some string starting with lowercase letter
//
// <E1> is a full logical expression as parsed by the function parse_logical_expression_string();
// the grammar for <E1> is defined in logic_expr.parser.rs.
//
// <num> is a non-negative decminal integer
//
// <Justification> ::=
//                      | Reit: <num>
//                      | And Intro: <num> {, <num>}
//                      | And Elim: <num>
//                      | Or Intro: <num>
//                      | Or Elim: <num>, <numrange> {, <numrange>}
//                      | Implies Intro: <numrange>
//                      | Implies Elim: <num>, <num>
//                      | Not Intro: <numrange>
//                      | Not Elim: <num>
//                      | Forall Intro: <numrange>
//                      | Forall Elim: <num>
//                      | Exists Intro: <num>
//                      | Exists Elim: <num>, <numrange>
//
// Note that Fitch proof lines are not very straightforward to parse, because it can be difficult
// to find the separation between the <E1> and the <Justification>. However, note that the Colon
// token only appears in the <Justification>, not in <E1>, <num> or <ConstantName>. Hence, if we
// want to parse a proof line, we first check whether there is a colon token in it. If there is,
// then we parse the justification first. For the rest, everything can just be done normally from
// left to right.

fn parse_proof_line(toks: &[Token]) -> Option<ProofLine> {
    if toks.contains(&Token::Colon) {
        // we know that in this case, <FitchProofLine> ::= <num> '|' { '|' } <E1> <Justification>
        // since only a Justification can legally contain a colon token
        let colon_index: usize = toks.iter().position(|t| t == &Token::Colon).unwrap();
        if colon_index < 4 {
            return None; // colon cannot appear this early
        }
        let toks_before_justification: &[Token];
        let toks_justification: &[Token];
        if let Token::Name(name) = &toks[colon_index - 1] {
            match name.as_str() {
                "Reit" => {
                    toks_before_justification = &toks[..colon_index - 1];
                    toks_justification = &toks[colon_index - 1..];
                }
                "Intro" | "Elim" => {
                    toks_before_justification = &toks[..colon_index - 2];
                    toks_justification = &toks[colon_index - 2..];
                }
                _ => {
                    return None; // nonexistent rule name
                }
            }

            if let (
                Token::Number(line_num),
                Token::ConseqVertBar(depth),
                Some(wff),
                Some(justific),
            ) = (
                toks_before_justification.first()?,
                toks_before_justification.get(1)?,
                parse_logical_expr(toks_before_justification.get(2..)?),
                parse_justification(toks_justification),
            ) {
                Some(ProofLine {
                    line_num: Some(*line_num),
                    depth: *depth,
                    is_premise: false,
                    is_fitch_bar_line: false,
                    sentence: Some(wff),
                    justification: Some(justific),
                    constant_between_square_brackets: None,
                })
            } else {
                None
            }
        } else {
            None // colon must be preceded by a rule name
        }
    } else {
        // Now we must be in one if these cases:
        //  <num> '|' { '|' } <E1>
        //  <num> '|' { '|' } '[' <ConstantName> ']' [ <E1> ]
        //  '|' { '|' } - { - }
        //  '|' { '|' }
        match toks.first()? {
            Token::Number(num) => {
                if let Token::ConseqVertBar(depth) = toks.get(1)? {
                    let mut const_betw_sqbr: Option<Term> = None;
                    let expression_start_index: usize = if let (
                        Some(Token::LSqBracket),
                        Some(Token::Name(name)),
                        Some(Token::RSqBracket),
                    ) =
                        (toks.get(2), toks.get(3), toks.get(4))
                    {
                        const_betw_sqbr = Some(Term::Atomic(name.to_string()));
                        if toks.len() == 5 {
                            // this premise contains only a boxed constant, no further expression:
                            // early exit
                            return Some(ProofLine {
                                line_num: Some(*num),
                                depth: *depth,
                                is_premise: true,
                                is_fitch_bar_line: false,
                                sentence: None,
                                justification: None,
                                constant_between_square_brackets: const_betw_sqbr,
                            });
                        }
                        5
                    } else {
                        2
                    };
                    if let Some(wff) = parse_logical_expr(toks.get(expression_start_index..)?) {
                        return Some(ProofLine {
                            line_num: Some(*num),
                            depth: *depth,
                            is_premise: true,
                            is_fitch_bar_line: false,
                            sentence: Some(wff),
                            justification: None,
                            constant_between_square_brackets: const_betw_sqbr,
                        });
                    }
                }

                None
            }
            Token::ConseqVertBar(depth) => {
                if toks[1..].iter().all(|t| t == &Token::Dash) {
                    Some(ProofLine {
                        line_num: None,
                        depth: *depth,
                        is_premise: false,
                        // if there is a dash, then this is a fitch bar. Otherwise it's an empty line.
                        is_fitch_bar_line: toks[1..].contains(&Token::Dash),
                        sentence: None,
                        justification: None,
                        constant_between_square_brackets: None,
                    })
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

fn parse_justification(toks: &[Token]) -> Option<Justification> {
    match (toks.first()?, toks.get(1)?, toks.get(2)?, toks.get(3)) {
        (Token::Name(name), Token::Colon, Token::Number(num), None) if name == "Reit" => {
            Some(Justification::Reit(*num))
        }
        (Token::And, Token::Name(name), Token::Colon, Some(Token::Number(num)))
            if name == "Intro" =>
        {
            let mut nums: Vec<usize> = vec![*num];
            let mut i = 4;
            while toks.get(i).is_some() {
                if toks[i] == Token::Comma {
                    if let Token::Number(next_num) = toks.get(i + 1)? {
                        nums.push(*next_num);
                    } else {
                        return None;
                    }
                } else {
                    return None;
                }
                i += 2;
            }
            Some(Justification::AndIntro(nums))
        }
        (Token::And, Token::Name(name), Token::Colon, Some(Token::Number(num)))
            if name == "Elim" && toks.get(4).is_none() =>
        {
            Some(Justification::AndElim(*num))
        }
        (Token::Or, Token::Name(name), Token::Colon, Some(Token::Number(num)))
            if name == "Intro" && toks.get(4).is_none() =>
        {
            Some(Justification::OrIntro(*num))
        }
        (Token::Or, Token::Name(name), Token::Colon, Some(Token::Number(num)))
            if name == "Elim" =>
        {
            let mut num_pairs: Vec<(usize, usize)> = vec![];
            let mut i = 4;
            toks.get(i)?; // should be at least one num-range provided
            while toks.get(i).is_some() {
                if toks[i] == Token::Comma {
                    if let (Token::Number(next_num1), Token::Dash, Token::Number(next_num2)) =
                        (toks.get(i + 1)?, toks.get(i + 2)?, toks.get(i + 3)?)
                    {
                        num_pairs.push((*next_num1, *next_num2));
                    } else {
                        return None;
                    }
                } else {
                    return None;
                }
                i += 4;
            }
            Some(Justification::OrElim(*num, num_pairs))
        }
        (Token::Implies, Token::Name(name), Token::Colon, Some(Token::Number(num1)))
            if name == "Intro" =>
        {
            if let (Token::Dash, Token::Number(num2), None) =
                (toks.get(4)?, toks.get(5)?, toks.get(6))
            {
                Some(Justification::ImpliesIntro((*num1, *num2)))
            } else {
                None
            }
        }
        (Token::Implies, Token::Name(name), Token::Colon, Some(Token::Number(num1)))
            if name == "Elim" =>
        {
            if let (Token::Comma, Token::Number(num2), None) =
                (toks.get(4)?, toks.get(5)?, toks.get(6))
            {
                Some(Justification::ImpliesElim(*num1, *num2))
            } else {
                None
            }
        }
        (Token::Not, Token::Name(name), Token::Colon, Some(Token::Number(num1)))
            if name == "Intro" =>
        {
            if let (Token::Dash, Token::Number(num2), None) =
                (toks.get(4)?, toks.get(5)?, toks.get(6))
            {
                Some(Justification::NotIntro((*num1, *num2)))
            } else {
                None
            }
        }
        (Token::Not, Token::Name(name), Token::Colon, Some(Token::Number(num)))
            if name == "Elim" && toks.get(4).is_none() =>
        {
            Some(Justification::NotElim(*num))
        }
        (Token::Forall, Token::Name(name), Token::Colon, Some(Token::Number(num1)))
            if name == "Intro" =>
        {
            if let (Token::Dash, Token::Number(num2), None) =
                (toks.get(4)?, toks.get(5)?, toks.get(6))
            {
                Some(Justification::ForallIntro((*num1, *num2)))
            } else {
                None
            }
        }
        (Token::Forall, Token::Name(name), Token::Colon, Some(Token::Number(num)))
            if name == "Elim" && toks.get(4).is_none() =>
        {
            Some(Justification::ForallElim(*num))
        }
        (Token::Exists, Token::Name(name), Token::Colon, Some(Token::Number(num)))
            if name == "Intro" && toks.get(4).is_none() =>
        {
            Some(Justification::ExistsIntro(*num))
        }
        (Token::Exists, Token::Name(name), Token::Colon, Some(Token::Number(num1)))
            if name == "Elim" =>
        {
            if let (Token::Comma, Token::Number(num2), Token::Dash, Token::Number(num3), None) = (
                toks.get(4)?,
                toks.get(5)?,
                toks.get(6)?,
                toks.get(7)?,
                toks.get(8),
            ) {
                Some(Justification::ExistsElim(*num1, (*num2, *num3)))
            } else {
                None
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_lexer_1() {
        assert_eq!(
            lex_logical_expr("   THIs is SoMe  SiLLY  test  "),
            Ok(vec![
                Token::Name("THIs".to_owned()),
                Token::Name("is".to_owned()),
                Token::Name("SoMe".to_owned()),
                Token::Name("SiLLY".to_owned()),
                Token::Name("test".to_owned())
            ])
        );
    }

    #[test]
    fn test_lexer_2() {
        assert_eq!(
            lex_logical_expr("   THIs is SoMe  S∀LLY  test  "),
            Ok(vec![
                Token::Name("THIs".to_owned()),
                Token::Name("is".to_owned()),
                Token::Name("SoMe".to_owned()),
                Token::Name("S".to_owned()),
                Token::Forall,
                Token::Name("LLY".to_owned()),
                Token::Name("test".to_owned())
            ])
        );
    }
    #[test]
    fn test_lexer_3() {
        assert_eq!(
            lex_logical_expr("   THIs is SoMe  S∀ ∀∀LLY  test  "),
            Ok(vec![
                Token::Name("THIs".to_owned()),
                Token::Name("is".to_owned()),
                Token::Name("SoMe".to_owned()),
                Token::Name("S".to_owned()),
                Token::Forall,
                Token::Forall,
                Token::Forall,
                Token::Name("LLY".to_owned()),
                Token::Name("test".to_owned())
            ])
        );
    }
    #[test]
    fn test_lexer_4() {
        assert_eq!(
            lex_logical_expr("∀x(P(x,a)→P(a,x))∨ (A∧ ItIsSunny∧¬∃y P(y,y))∨a=c"),
            Ok(vec![
                Token::Forall,
                Token::Name("x".to_owned()),
                Token::LPar,
                Token::Name("P".to_owned()),
                Token::LPar,
                Token::Name("x".to_owned()),
                Token::Comma,
                Token::Name("a".to_owned()),
                Token::RPar,
                Token::Implies,
                Token::Name("P".to_owned()),
                Token::LPar,
                Token::Name("a".to_owned()),
                Token::Comma,
                Token::Name("x".to_owned()),
                Token::RPar,
                Token::RPar,
                Token::Or,
                Token::LPar,
                Token::Name("A".to_owned()),
                Token::And,
                Token::Name("ItIsSunny".to_owned()),
                Token::And,
                Token::Not,
                Token::Exists,
                Token::Name("y".to_owned()),
                Token::Name("P".to_owned()),
                Token::LPar,
                Token::Name("y".to_owned()),
                Token::Comma,
                Token::Name("y".to_owned()),
                Token::RPar,
                Token::RPar,
                Token::Or,
                Token::Name("a".to_owned()),
                Token::Equals,
                Token::Name("c".to_owned()),
            ])
        );
    }

    #[test]
    fn test_parser_1() {
        assert_eq!(
            parse_logical_expression_string("A∧B"),
            Some(Wff::And(vec![
                Wff::Atomic("A".to_string()),
                Wff::Atomic("B".to_string())
            ]))
        );
    }
    #[test]
    fn test_parser_2() {
        assert_eq!(
            parse_logical_expression_string("AB"),
            Some(Wff::Atomic("AB".to_string()),)
        );
    }
    #[test]
    fn test_parser_3() {
        assert_eq!(parse_logical_expression_string("a∧B"), None);
    }
    #[test]
    fn test_parser_4() {
        assert_eq!(parse_logical_expression_string("aAAA"), None);
    }
    #[test]
    fn test_parser_5() {
        assert_eq!(
            parse_logical_expression_string("A∨B"),
            Some(Wff::Or(vec![
                Wff::Atomic("A".to_string()),
                Wff::Atomic("B".to_string())
            ]))
        );
    }
    #[test]
    fn test_parser_6() {
        assert_eq!(parse_logical_expression_string("A∨∧B"), None);
    }
    #[test]
    fn test_parser_7() {
        assert_eq!(
            parse_logical_expression_string("A→B"),
            Some(Wff::Implies(
                Box::new(Wff::Atomic("A".to_string())),
                Box::new(Wff::Atomic("B".to_string()))
            ))
        );
    }
    #[test]
    fn test_parser_8() {
        assert_eq!(parse_logical_expression_string("A→→→B"), None);
    }
    #[test]
    fn test_parser_9() {
        assert_eq!(
            parse_logical_expression_string("∀x(∀y P(x,y))"),
            Some(Wff::Forall(
                "x".to_string(),
                Box::new(Wff::Forall(
                    "y".to_string(),
                    Box::new(Wff::PredApp(
                        "P".to_string(),
                        vec![Term::Atomic("x".to_string()), Term::Atomic("y".to_string())]
                    ))
                ))
            ))
        );
        assert_eq!(
            parse_logical_expression_string("∀x(∀y P(x,y))"),
            parse_logical_expression_string("∀x∀y P(x,y)")
        );
        assert_eq!(
            parse_logical_expression_string("∀x(∀y P(x,y))"),
            parse_logical_expression_string("(∀x∀y P(x,y))")
        );
    }
    #[test]
    fn test_parser_10() {
        assert_eq!(parse_logical_expression_string("∀(x∀y P(x,y))"), None);
    }
    #[test]
    fn test_parser_11() {
        // the most insane test ever
        let expected_result = Some(Wff::Or(vec![
            (Wff::Forall(
                "x".to_string(),
                Box::new(Wff::Implies(
                    Box::new(Wff::PredApp(
                        "P".to_string(),
                        vec![
                            Term::Atomic("a".to_string()),
                            Term::Atomic("b".to_string()),
                            Term::Atomic("x".to_string()),
                        ],
                    )),
                    Box::new(Wff::PredApp(
                        "Q".to_string(),
                        vec![
                            Term::FuncApp("f".to_string(), vec![Term::Atomic("a".to_string())]),
                            Term::FuncApp(
                                "f".to_string(),
                                vec![
                                    Term::Atomic("b".to_string()),
                                    Term::Atomic("c".to_string()),
                                    Term::Atomic("d".to_string()),
                                ],
                            ),
                            Term::FuncApp("g".to_string(), vec![Term::Atomic("x".to_string())]),
                        ],
                    )),
                )),
            )),
            (Wff::Equals(
                Term::FuncApp(
                    "f".to_string(),
                    vec![Term::Atomic("a".to_string()), Term::Atomic("b".to_string())],
                ),
                Term::FuncApp(
                    "f".to_string(),
                    vec![
                        Term::Atomic("bla".to_string()),
                        Term::Atomic("c".to_string()),
                    ],
                ),
            )),
            (Wff::Not(Box::new(Wff::Exists(
                "x".to_string(),
                Box::new(Wff::Not(Box::new(Wff::Not(Box::new(Wff::Not(Box::new(
                    Wff::Exists(
                        "y".to_string(),
                        Box::new(Wff::Not(Box::new(Wff::Not(Box::new(Wff::Forall(
                            "z".to_string(),
                            Box::new(Wff::Not(Box::new(Wff::Not(Box::new(Wff::Implies(
                                Box::new(Wff::PredApp(
                                    "P".to_string(),
                                    vec![
                                        Term::FuncApp(
                                            "f".to_string(),
                                            vec![Term::Atomic("x".to_string())],
                                        ),
                                        Term::FuncApp(
                                            "f".to_string(),
                                            vec![Term::Atomic("y".to_string())],
                                        ),
                                        Term::FuncApp(
                                            "f".to_string(),
                                            vec![Term::Atomic("z".to_string())],
                                        ),
                                    ],
                                )),
                                Box::new(Wff::Not(Box::new(Wff::And(vec![
                                    Wff::PredApp(
                                        "A".to_string(),
                                        vec![Term::Atomic("x".to_string())],
                                    ),
                                    Wff::PredApp(
                                        "B".to_string(),
                                        vec![Term::Atomic("y".to_string())],
                                    ),
                                ])))),
                            )))))),
                        )))))),
                    ),
                ))))))),
            )))),
        ]));

        // correct
        let expr1 = "∀x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))";

        // correct, same as expr1 but with a lot of spaces
        let expr2 = " ∀ x ( P ( a , b , x )   → Q ( f ( a ) , f ( b , c , d ) , g ( x ) ) ) ∨ f ( a , b ) = f ( bla , c ) ∨ ¬ ∃ x ¬ ¬ ¬ ∃ y ¬ ¬ ∀ z ¬ ¬ ( P ( f ( x ) , f ( y ) , f ( z ) ) → ¬ ( A ( x ) ∧ B ( y ) ) ) ";

        // wrong, misses a bracket in the end
        let expr3 = "∀x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y))";

        // correct, same as expr1 but with a lot of extra brackets
        let expr4 = "((∀x((P(a,b,x))→((Q(f(a),f(b,c,d),g(x)))))∨((((((f(a,b)=f(bla,c)))))))∨(¬(∃x(¬(¬(¬(∃y(¬(¬(∀z(¬(¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y))))))))))))))))";

        // wrong, same as expr1 but with brackets in a place where they shouldn't be
        let expr5 = "∀x(P((a),b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))";

        // wrong, same as expr1 but with brackets in a place where they shouldn't be
        let expr6 = "∀x(P((a,b,x))→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))";

        // wrong, same as expr1 but with brackets in a place where they shouldn't be
        let expr7 = "∀x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃(x)¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))";

        // wrong, same as expr1 but with one ) removed
        let expr8 = "∀x(P(a,b,x→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))";

        // wrong, same as expr1 but with one → removed
        let expr9 = "∀x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))¬(A(x)∧B(y)))";

        assert_eq!(parse_logical_expression_string(expr1), expected_result);
        assert_eq!(parse_logical_expression_string(expr2), expected_result);
        assert_eq!(parse_logical_expression_string(expr3), None);
        assert_eq!(parse_logical_expression_string(expr4), expected_result);
        assert_eq!(parse_logical_expression_string(expr5), None);
        assert_eq!(parse_logical_expression_string(expr6), None);
        assert_eq!(parse_logical_expression_string(expr7), None);
        assert_eq!(parse_logical_expression_string(expr8), None);
        assert_eq!(parse_logical_expression_string(expr9), None);
    }
    #[test]
    fn test_parser_12() {
        assert_eq!(parse_logical_expression_string("A∨B∧C"), None);
    }
    #[test]
    fn test_parser_13() {
        assert_eq!(parse_logical_expression_string("A∧B∨B"), None);
    }
    #[test]
    fn test_parser_14() {
        assert_eq!(parse_logical_expression_string("a=b=b"), None);
    }
    #[test]
    fn test_parser_15() {
        assert_eq!(
            parse_logical_expression_string("a=b"),
            Some(Wff::Equals(
                Term::Atomic("a".to_string()),
                Term::Atomic("b".to_string())
            ))
        );
    }

    #[test]
    fn test_justification_parser_or_elim() {
        assert_eq!(
            parse_justification(&lex_logical_expr("∨Elim:42,43-44").unwrap()),
            Some(Justification::OrElim(42, vec![(43, 44)]))
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∨Elim:42,43-44,45-46,47-48").unwrap()),
            Some(Justification::OrElim(
                42,
                vec![(43, 44), (45, 46), (47, 48)]
            ))
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∨Elim:42,43-44,45-46,47,48").unwrap()),
            None
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∨Elim:42,43-44,45-46-47-48").unwrap()),
            None
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∨Elim:42-43-44,45-46,47-48").unwrap()),
            None
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∨Elim-42,43-44,45-46,47-48").unwrap()),
            None
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∨Elim:42,43-44,45-46,47-48,").unwrap()),
            None
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∨Elim:42,43-44,45-46,47-48,49").unwrap()),
            None
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∨Elim:42,43-44,45-46,47-48,49-").unwrap()),
            None
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∨Elim:42").unwrap()),
            None
        );
    }
    #[test]
    fn test_justification_parser_and_intro() {
        assert_eq!(
            parse_justification(&lex_logical_expr("∧Intro:42,43,44").unwrap()),
            Some(Justification::AndIntro(vec![42, 43, 44]))
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∧Intro:42,43").unwrap()),
            Some(Justification::AndIntro(vec![42, 43]))
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∧Intro:42").unwrap()),
            // TODO: decide whether i want to keep behavior like this (a "unary conjunction")
            Some(Justification::AndIntro(vec![42]))
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∧Intro:42-43").unwrap()),
            None
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("∧Intro:").unwrap()),
            None
        );
    }
    #[test]
    fn test_justification_parser_exists_elim() {
        assert_eq!(
            parse_justification(&lex_logical_expr("∃Elim:42,43-44").unwrap()),
            Some(Justification::ExistsElim(42, (43, 44)))
        );
    }
    #[test]
    fn test_justification_parser_implies_elim() {
        assert_eq!(
            parse_justification(&lex_logical_expr("→Elim:42,43").unwrap()),
            Some(Justification::ImpliesElim(42, 43))
        );
        assert_eq!(
            parse_justification(&lex_logical_expr("→Elim:42,43,").unwrap()),
            None
        );
    }
}
