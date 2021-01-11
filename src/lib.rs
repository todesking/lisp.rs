#[macro_use]
pub mod value;
pub mod eval;
pub mod global_env;
pub mod local_env;
pub mod parser;

use std::rc::Rc;

pub fn parse(src: &str) -> Result<parser::Expr, parser::ParseError> {
    src.parse::<parser::Expr>()
}

pub fn predef() -> global_env::GlobalEnv {
    global_env::GlobalEnv::predef()
}

pub fn eval(
    expr: &parser::Expr,
    global: &mut global_env::GlobalEnv,
) -> Result<Rc<value::Value>, eval::EvalError> {
    eval::eval(&expr.into(), global)
}
