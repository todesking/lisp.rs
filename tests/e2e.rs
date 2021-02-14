fn run_test_str(src: &str) -> Result<(), Box<dyn std::error::Error>> {
    let exprs = lisprs::parse_all(src)?;

    let mut global = lisprs::predef();
    for expr in exprs {
        lisprs::eval(&expr, &mut global).map_err(|e| {
            println!("Test failed.");
            println!("  Expr: {}", expr.to_string());
            println!("     => {}", e.to_string());
            e
        })?;
    }

    Ok(())
}

macro_rules! testcase {
    ($name:tt) => {
        #[test]
        fn $name() -> Result<(), std::boxed::Box<dyn std::error::Error>> {
            run_test_str(include_str!(concat!("e2e/", stringify!($name), ".lisp")))
        }
    };
}

mod test {
    use super::run_test_str;

    testcase!(arithmetic);
    testcase!(assert_error);
    testcase!(letrec);
    testcase!(list_ops);
    testcase!(macros);
    testcase!(pattern_match);
    testcase!(quasiquote);
    testcase!(variable_lookup);
    testcase!(gensym);
}
