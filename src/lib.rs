#[macro_use]
pub mod value;
pub mod eval;
pub mod global_env;
pub mod local_env;
pub mod parser;

pub fn parse(src: &str) -> Result<value::Value, parser::ParseError> {
    src.parse::<value::Value>()
}

pub fn predef() -> global_env::GlobalEnv {
    global_env::GlobalEnv::predef()
}

pub fn eval(
    expr: &value::Value,
    global: &mut global_env::GlobalEnv,
) -> Result<value::Value, eval::EvalError> {
    eval::eval(expr, global)
}
