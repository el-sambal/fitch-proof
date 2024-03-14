use std::iter;
use std::iter::from_fn;

#[derive(PartialEq, Debug)]
pub enum Term {
    Atomic(String),             // a variable or a constant
    FuncApp(String, Vec<Term>), // function application
}

#[derive(PartialEq, Debug)]
// well-formed formula (well, you have to hope it's well-formed...)
pub enum Wff {
    And(Vec<Wff>),
    Or(Vec<Wff>),
    Implies(Box<Wff>, Box<Wff>),
    Not(Box<Wff>),
    Forall(String, Box<Wff>),
    Exists(String, Box<Wff>),
    Atomic(String),             // a nullary predicate (proposition)
    PredApp(String, Vec<Term>), // n-ary predicate application (n >= 1)
    Equals(Term, Term),         // the equality function applied to two terms
}

pub fn parse_logical_expression_string(expr: &str) -> Option<Wff> {
    if let Ok(toks) = lex_logical_expr(expr) {
        return parse_logical_expr(&toks);
    }
    None
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
    Comma,
    Equals,
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
                        input_iter.by_ref().next_if(|c| c.is_alphabetic())
                    }))
                    .collect::<String>();
                toks.push(Token::Name(name));
            }
            _ => {
                let mut err: String = "invalid character found: ".to_owned();
                err.push_str(&ch.to_string());
                return Err(err);
            }
        }
    }

    Ok(toks)
}

// Converts token list into syntax 'tree' (Wff) using recursive descent parsing.
//
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
//
fn parse_logical_expr(toks: &[Token]) -> Option<Wff> {
    if let Some((wff, _)) = parse_e1(toks) {
        return Some(wff);
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

    /*
    // forall <VariableOrConstantName> <E3>
    if toks.first()? == &Token::Forall {
        return match toks.get(1)? {
            Token::Name(name) if name.chars().next()?.is_lowercase() => {
                if let Some((wff, rem_toks)) = parse_e3(toks.get(2..)?) {
                    return Some((Wff::Forall(name.to_owned(), Box::new(wff)), rem_toks));
                }
                None
            }
            _ => None,
        };
    }

    // exists <VariableOrConstantName> <E3>
    if toks.first()? == &Token::Exists {
        return match toks.get(1)? {
            Token::Name(name) if name.chars().next()?.is_lowercase() => {
                if let Some((wff, rem_toks)) = parse_e3(toks.get(2..)?) {
                    return Some((Wff::Exists(name.to_owned(), Box::new(wff)), rem_toks));
                }
                None
            }
            _ => None,
        };
    }
    */

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
}
