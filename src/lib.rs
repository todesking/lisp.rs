#[macro_use]
mod value;
mod ast;
mod compile;
mod error;
mod eval;
mod global_env;
mod local_env;
mod name;
mod parser;
mod predef;

pub use ast::TopAst;
pub use compile::build_top_ast;
pub use error::EvalError;
pub use eval::eval;
pub use eval::eval_top_ast;
pub use global_env::GlobalEnv;
pub use global_env::GlobalWrite;
pub use parser::ParseError;
pub use parser::Parser;
pub use predef::load_predef;
pub use value::Value;

pub fn parse(src: &str) -> Result<Value, ParseError> {
    src.parse::<value::Value>()
}

pub fn parse_all(src: &str) -> Result<Vec<value::Value>, ParseError> {
    let mut parser = Parser::new();
    parser.parse_all(src)
}

pub fn predef() -> GlobalEnv {
    let mut global = GlobalEnv::new();
    load_predef(&mut global);
    global
}

pub fn eval_str_or_panic(src: &str, global: &mut GlobalEnv) -> Value {
    let expr = parse(src).expect("Parse failed");
    eval(&expr, global).expect("Eval failed")
}

pub fn eval_str_all_or_panic(src: &str, global: &mut GlobalEnv) {
    let exprs = parse_all(src).expect("Parse failed");
    for e in exprs {
        eval(&e, global).expect("Eval failed");
    }
}
