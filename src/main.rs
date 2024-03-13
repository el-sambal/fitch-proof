use std::iter;
use std::iter::from_fn;

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

#[derive(PartialEq, Debug)]
enum Term {
    Atomic(String),             // a variable or a constant
    FuncApp(String, Vec<Term>), // function application
}

#[derive(PartialEq, Debug)]
// well-formed formula (well, you have to hope it's well-formed...)
enum Wff {
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

// Converts token list into syntax 'tree' (Wff) using recursive descent parsing.
//
// The grammar: (brackets denote tokens, but {} is EBNF notation for 0 or more times)
//
// <E1> ::=
//            forall <N> <E2>
//          | exists <N> <E2>
//          | not <E2>
//          | <E2> {and <E2>}
//          | <E2> {or <E2>}
//          | <E2> implies <E2>
//          | <E2>
//          | <Term> equals <Term>
//
// <E2> ::=
//            ( <E1> )
//          | <PredicateName> ( <Term> {, <Term>} )
//          | <AtomicPropositionName>
//
// <Term> ::=
//              <FunctionName> ( <Term> {, <Term>} )
//            | <VariableOrConstantName>
//
// <FunctionName> : some string starting with a lowercase letter
// <VariableOrConstantName> : some string starting with a lowercase letter
// <PredicateName> : some string starting with an UPPERCASE letter
// <AtomicPropositionName> : some string starting with an UPPERCASE letter
fn parse_logical_expr(toks: &[Token]) -> Option<Wff> {
    if let Some((wff, _)) = parse_e1(toks) {
        return Some(wff)
    }
    None
}

fn parse_e1(toks: &[Token]) -> Option<(Wff, &[Token])> {
    if toks.is_empty() {
        return None;
    }

    if toks[0] == Token::Forall {

    }



    todo!();
}

fn main() {
    println!("Hello, world!");
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
}
