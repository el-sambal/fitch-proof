mod parser;
fn main() {
    println!(
        "{:?}",
        parser::parse_logical_expression_string(
            "∀ x∀ x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)"
        )
    );
    println!("Hello, world!");
}
