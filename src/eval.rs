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

impl Value {
    fn cons(car: Value, cdr: Value) -> Value {
        Value::Cons(Rc::new(car), Rc::new(cdr))
    }
}

impl From<i32> for Value {
    fn from(x: i32) -> Value {
        Value::Int(x)
    }
}

impl<T1, T2> From<(T1, T2)> for Value
where
    T1: Into<Value>,
    T2: Into<Value>,
{
    fn from(x: (T1, T2)) -> Value {
        Value::cons(x.0.into(), x.1.into())
    }
}

impl<T: Into<Value>> From<Vec<T>> for Value {
    fn from(x: Vec<T>) -> Value {
        x.into_iter()
            .rev()
            .fold(Value::Nil, |a, x| Value::cons(x.into(), a))
    }
}

#[macro_export]
macro_rules! list {
    () =>  { Value::Nil };
    ($x: expr) => { Value::cons(Value::from($x), Value::Nil) };
    ($x: expr, $($xs: expr),+) => { Value::cons(Value::from($x), list!($($xs),+)) };
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
    fn test_list_macro() {
        assert_eq!(list!(), Value::Nil);
        assert_eq!(list!(1), Value::cons(Value::Int(1), Value::Nil));
        assert_eq!(
            list!(Value::Int(1), 2),
            Value::cons(Value::Int(1), Value::cons(Value::Int(2), Value::Nil))
        );
    }

    #[test]
    fn test_num() {
        let mut env = new_env();
        eval_str("1", &mut env).should_ok(1.into());
    }

    #[test]
    fn test_sym() {
        let mut env = new_env();
        env.insert("x".to_string(), 123.into());

        eval_str("x", &mut env).should_ok(123.into());
    }
}
