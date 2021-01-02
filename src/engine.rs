use std::rc::Rc;
use crate::parser::Expr;

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
    Cons(Rc<Value>, Rc<Value>)
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
        Expr::Sym(key) =>
            env.lookup(key).cloned()
            .ok_or(EvalError::KeyNotFound(key.to_string())),
        Expr::Nil => Err(EvalError::Nil),
        Expr::Cons(f, args) =>
            unimplemented!()
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

    #[test]
    fn test_num() {
        let env = new_env();
        let e = eval(&Expr::int(0), &env);
        assert_eq!(e, Ok(Value::Int(0)));
    }

    #[test]
    fn test_sym() {
        let mut env = new_env();
        env.insert("x".to_string(), Value::Int(123));

        let e = eval(&Expr::sym("x"), &env);
        assert_eq!(e, Ok(Value::Int(123)));
    }
}
