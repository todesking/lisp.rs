use crate::parser::Expr;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub enum EvalError {
    KeyNotFound(String),
    ImproperArgs,
    ArgumentSize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(i32),
    Sym(String),
    Nil,
    Cons(Rc<Value>, Rc<Value>),
}

impl Value {
    fn cons<T1: Into<Value>, T2: Into<Value>>(car: T1, cdr: T2) -> Value {
        Value::Cons(Rc::new(car.into()), Rc::new(cdr.into()))
    }
    fn to_vec(&self) -> Option<Vec<Rc<Value>>> {
        let mut rest = self;
        let mut values = Vec::new();
        while let Value::Cons(car, cdr) = rest {
            rest = cdr;
            values.push(car.clone());
        }
        match rest {
            Value::Nil => Some(values),
            _ => None,
        }
    }
}

pub trait ToValue {
    fn to_value(self) -> Value;
}

impl<T: ToValue> From<T> for Value {
    fn from(x: T) -> Value {
        x.to_value()
    }
}

impl ToValue for &i32 {
    fn to_value(self) -> Value {
        Value::Int(*self)
    }
}

impl ToValue for i32 {
    fn to_value(self) -> Value {
        Value::Int(self)
    }
}

impl<'a, T> ToValue for &'a Vec<T>
where
    &'a T: Into<Value>,
{
    fn to_value(self) -> Value {
        self.iter().rev().fold(Value::Nil, |a, x| Value::cons(x, a))
    }
}

impl<'a> ToValue for &'a Vec<Rc<Value>> {
    fn to_value(self) -> Value {
        self.iter()
            .rev()
            .fold(Value::Nil, |a, x| Value::Cons(x.clone(), Rc::new(a)))
    }
}

impl ToValue for &Expr {
    fn to_value(self) -> Value {
        match self {
            Expr::Int(n) => n.into(),
            Expr::Sym(s) => Value::Sym(s.clone()),
            Expr::Nil => Value::Nil,
            Expr::Cons(car, cdr) => Value::cons(car.as_ref(), cdr.as_ref()),
        }
    }
}

#[macro_export]
macro_rules! list {
    () =>  { Value::Nil };
    ($x: expr) => { Value::cons(Value::from($x), Value::Nil) };
    ($x: expr, $($xs: expr),+) => { Value::cons(Value::from($x), list!($($xs),+)) };
}

pub type Result = std::result::Result<Rc<Value>, EvalError>;

pub trait Env {
    fn lookup<T: AsRef<str>>(&self, key: &T) -> Option<Rc<Value>>;
}

impl Env for std::collections::HashMap<String, Rc<Value>> {
    fn lookup<T: AsRef<str>>(&self, key: &T) -> Option<Rc<Value>> {
        self.get(key.as_ref()).cloned()
    }
}

pub fn eval<E: Env>(e: &Value, env: &E) -> Result {
    match e {
        Value::Int(n) => Ok(Rc::new(Value::Int(*n))),
        Value::Nil => Ok(Rc::new(Value::Nil)),
        Value::Sym(key) => env
            .lookup(key)
            .ok_or_else(|| EvalError::KeyNotFound(key.to_string())),
        Value::Cons(car, cdr) => match car.as_ref() {
            Value::Sym(name) if name == "quote" => match cdr.as_ref().to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [x] => Ok(x.clone()),
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            _ => unimplemented!(),
        },
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::Expr;
    use std::collections::HashMap;

    fn new_env() -> HashMap<String, Rc<Value>> {
        HashMap::new()
    }

    fn eval_str<E: Env>(s: &str, env: &mut E) -> Result {
        let expr = s.parse::<Expr>().unwrap();
        eval(&(&expr).into(), env)
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
            assert_eq!(self, &Ok(Rc::new(value)));
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
        env.insert("x".to_string(), Rc::new(123.into()));

        eval_str("x", &mut env).should_ok(123.into());
    }

    #[test]
    fn test_nil() {
        let mut env = new_env();
        eval_str("()", &mut env).should_ok(Value::Nil);
    }

    #[test]
    fn test_quote() {
        let mut env = new_env();

        eval_str("'1", &mut env).should_ok(1.into());
        eval_str("'(1 2)", &mut env).should_ok((&vec![1, 2]).into());
        eval_str("(quote (1 2))", &mut env).should_ok((&vec![1, 2]).into());
        eval_str("(quote 1 . 2)", &mut env).should_error(EvalError::ImproperArgs);
        eval_str("(quote . 1)", &mut env).should_error(EvalError::ImproperArgs);
        eval_str("(quote 1 2)", &mut env).should_error(EvalError::ArgumentSize);
    }
}
