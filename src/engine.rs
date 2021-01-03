use crate::parser::Expr;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub enum EvalError {
    Nil,
    KeyNotFound(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(i32),
    Sym(String),
    Nil,
    Cons(Rc<Value>, Rc<Value>),
}

pub type Result = std::result::Result<Value, EvalError>;

pub trait Env {
    fn lookup<T: AsRef<str>>(&self, key: &T) -> Option<&Value>;
}

impl Env for std::collections::HashMap<String, Value> {
    fn lookup<T: AsRef<str>>(&self, key: &T) -> Option<&Value> {
        self.get(key.as_ref())
    }
}

pub fn eval<E: Env>(e: &Expr, env: &E) -> Result {
    match e {
        Expr::Int(n) => Ok(Value::Int(*n)),
        Expr::Sym(key) => env
            .lookup(key)
            .cloned()
            .ok_or_else(|| EvalError::KeyNotFound(key.to_string())),
        Expr::Nil => Err(EvalError::Nil),
        Expr::Cons(_f, _args) => unimplemented!(),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::Expr;
    use std::collections::HashMap;

    fn new_env() -> HashMap<String, Value> {
        HashMap::new()
    }

    fn eval_str<E: Env>(s: &str, env: &mut E) -> Result {
        let expr = s.parse::<Expr>().unwrap();
        eval(&expr, env)
    }

    trait Assertion {
        fn should_error(&self, err: EvalError);
        fn should_ok(&self, value: Value);
    }
    impl Assertion for Result {
        fn should_error(&self, err: EvalError) {
            assert_eq!(self, &Err(err));
        }
        fn should_ok(&self, value: Value) {
            assert_eq!(self, &Ok(value));
        }
    }

    #[test]
    fn test_num() {
        let mut env = new_env();
        eval_str("1", &mut env).should_ok(Value::Int(1));
    }

    #[test]
    fn test_sym() {
        let mut env = new_env();
        env.insert("x".to_string(), Value::Int(123));

        eval_str("x", &mut env).should_ok(Value::Int(123));
    }
}
