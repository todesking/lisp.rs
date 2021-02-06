#[macro_use]
pub mod value;
pub mod eval;
pub mod parser;
pub mod predef;

pub fn parse(src: &str) -> Result<value::Value, parser::ParseError> {
    src.parse::<value::Value>()
}

pub fn parse_all(src: &str) -> Result<Vec<value::Value>, parser::ParseError> {
    let mut parser = parser::Parser::new();
    parser.parse_all(src)
}

pub fn predef() -> eval::GlobalEnv {
    let mut global = eval::GlobalEnv::new();
    predef::load(&mut global);
    global
}

pub fn eval(
    expr: &value::Value,
    global: &mut eval::GlobalEnv,
) -> Result<value::Value, eval::EvalError> {
    eval::eval(expr, global)
}

pub fn eval_str_or_panic(src: &str, global: &mut eval::GlobalEnv) -> value::Value {
    let expr = parse(src).expect("Parse failed");
    eval(&expr, global).expect("Eval failed")
}
