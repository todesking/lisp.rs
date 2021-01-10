use crate::parser::Expr;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub enum EvalError {
    VariableNotFound(String),
    ImproperArgs,
    ArgumentSize,
    SymbolRequired,
    InvalidParamList,
    CantApply,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(i32),
    Sym(String),
    Nil,
    Cons(Rc<Value>, Rc<Value>),
    Lambda(Vec<String>, Vec<Rc<Value>>, Option<Rc<LocalEnv>>),
}

impl Value {
    fn cons<T1: Into<Value>, T2: Into<Value>>(car: T1, cdr: T2) -> Value {
        Value::Cons(Rc::new(car.into()), Rc::new(cdr.into()))
    }
    fn to_vec(&self) -> Option<Vec<Rc<Value>>> {
        if self == &Value::Nil {
            return Some(vec![]);
        }

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

pub struct GlobalEnv {
    values: std::collections::HashMap<String, Rc<Value>>,
}

impl GlobalEnv {
    pub fn new() -> GlobalEnv {
        GlobalEnv {
            values: std::collections::HashMap::new(),
        }
    }
    pub fn lookup<T: AsRef<str>>(&self, key: &T) -> Option<Rc<Value>> {
        self.values.get(key.as_ref()).cloned()
    }
    pub fn set<T: Into<String>>(&mut self, key: T, value: Rc<Value>) {
        self.values.insert(key.into(), value);
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct LocalEnv {
    values: std::collections::HashMap<String, Rc<Value>>,
    parent: Option<Rc<LocalEnv>>,
}

impl LocalEnv {
    fn new(param_names: &[String], args: &[Rc<Value>], parent: Option<Rc<LocalEnv>>) -> LocalEnv {
        let mut values = std::collections::HashMap::new();
        for (k, v) in param_names.iter().zip(args) {
            values.insert(k.clone(), v.clone());
        }
        LocalEnv { values, parent }
    }
    fn lookup<T: AsRef<str>>(&self, key: &T) -> Option<Rc<Value>> {
        self.values
            .get(key.as_ref())
            .cloned()
            .or_else(|| match &self.parent {
                None => None,
                Some(l) => l.lookup(key),
            })
    }
}

pub fn eval(e: &Value, global: &mut GlobalEnv) -> Result {
    eval_local(e, global, None)
}

fn eval_local(e: &Value, global: &mut GlobalEnv, local: Option<&Rc<LocalEnv>>) -> Result {
    match e {
        Value::Int(n) => Ok(Rc::new(Value::Int(*n))),
        Value::Nil => Ok(Rc::new(Value::Nil)),
        Value::Sym(key) => local
            .map_or_else(|| global.lookup(key), |l| l.lookup(key))
            .ok_or_else(|| EvalError::VariableNotFound(key.to_string())),
        Value::Lambda(_, _, _) => unimplemented!(),
        Value::Cons(car, cdr) => match car.as_ref() {
            Value::Sym(name) if name == "quote" => match cdr.as_ref().to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [x] => Ok(x.clone()),
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            Value::Sym(name) if name == "define" => match cdr.to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [name, value] => match name.as_ref() {
                        Value::Sym(name) => {
                            global.set(name, value.clone());
                            Ok(Rc::new(Value::Nil))
                        }
                        _ => Err(EvalError::SymbolRequired),
                    },
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            Value::Sym(name) if name == "lambda" => match cdr.as_ref() {
                Value::Cons(params, body) => match params.to_vec() {
                    None => Err(EvalError::InvalidParamList),
                    Some(params) => {
                        let mut param_names = vec![];
                        for p in params.iter() {
                            match p.as_ref() {
                                Value::Sym(name) => param_names.push(name),
                                _ => break,
                            }
                        }
                        if param_names.len() != params.len() {
                            Err(EvalError::SymbolRequired)
                        } else {
                            match body.to_vec() {
                                None => Err(EvalError::ImproperArgs),
                                Some(body) => match body.as_slice() {
                                    [] => Err(EvalError::ArgumentSize),
                                    body => eval_lambda(&param_names, body, local),
                                },
                            }
                        }
                    }
                },
                Value::Nil => Err(EvalError::ArgumentSize),
                _ => Err(EvalError::ImproperArgs),
            },
            f => match cdr.to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => {
                    let f = eval_local(f, global, local)?;
                    let mut arg_values = vec![];
                    for arg in args.iter() {
                        let a = eval_local(arg, global, local)?;
                        arg_values.push(a);
                    }
                    eval_apply(&f, &arg_values, global)
                }
            },
        },
    }
}

fn eval_lambda(
    param_names: &[&String],
    body: &[Rc<Value>],
    local: Option<&Rc<LocalEnv>>,
) -> Result {
    let param_names: Vec<String> = param_names.iter().map(|x| (*x).clone()).collect();
    let body: Vec<Rc<Value>> = body.to_vec();
    Ok(Rc::new(Value::Lambda(param_names, body, local.cloned())))
}

fn eval_apply(f: &Rc<Value>, args: &[Rc<Value>], global: &mut GlobalEnv) -> Result {
    match f.as_ref() {
        Value::Lambda(param_names, body, local) => {
            if args.len() != param_names.len() {
                Err(EvalError::ArgumentSize)
            } else {
                let local = Rc::new(LocalEnv::new(param_names, args, local.clone()));
                let mut e = Rc::new(Value::Nil);
                for b in body {
                    e = eval_local(b, global, Some(&local))?;
                }
                Ok(e)
            }
        }
        _ => Err(EvalError::CantApply),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::Expr;

    fn eval_str(s: &str, env: &mut GlobalEnv) -> Result {
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
        let mut env = GlobalEnv::new();
        eval_str("1", &mut env).should_ok(1.into());
    }

    #[test]
    fn test_sym() {
        let mut env = GlobalEnv::new();
        env.set("x".to_string(), Rc::new(123.into()));

        eval_str("x", &mut env).should_ok(123.into());
    }

    #[test]
    fn test_nil() {
        let mut env = GlobalEnv::new();
        eval_str("()", &mut env).should_ok(Value::Nil);
    }

    #[test]
    fn test_quote() {
        let mut env = GlobalEnv::new();

        eval_str("'1", &mut env).should_ok(1.into());
        eval_str("'(1 2)", &mut env).should_ok((&vec![1, 2]).into());
        eval_str("(quote (1 2))", &mut env).should_ok((&vec![1, 2]).into());
        eval_str("(quote 1 . 2)", &mut env).should_error(EvalError::ImproperArgs);
        eval_str("(quote . 1)", &mut env).should_error(EvalError::ImproperArgs);
        eval_str("(quote 1 2)", &mut env).should_error(EvalError::ArgumentSize);
    }

    #[test]
    fn test_define() {
        let mut env = GlobalEnv::new();
        eval_str("x", &mut env).should_error(EvalError::VariableNotFound("x".into()));
        eval_str("(define x 1)", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1.into());

        eval_str("(define x 2 3)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(define 1 2)", &mut env).should_error(EvalError::SymbolRequired);
    }

    #[test]
    fn test_lambda_error() {
        let mut env = GlobalEnv::new();

        eval_str("(lambda)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(lambda () 1 . 2)", &mut env).should_error(EvalError::ImproperArgs);
        eval_str("(lambda (x))", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(lambda x 1)", &mut env).should_error(EvalError::InvalidParamList);
        eval_str("(lambda 1 1)", &mut env).should_error(EvalError::InvalidParamList);
    }
    #[test]
    fn test_lambda_simple() {
        let mut env = GlobalEnv::new();

        eval_str("((lambda () 1))", &mut env).should_ok(1.into());
        eval_str("((lambda (x) x) 1)", &mut env).should_ok(1.into());
        eval_str("((lambda (x y) x) 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("((lambda (x y) y) 1 2)", &mut env).should_ok(2.into());
    }

    #[test]
    fn test_lambda_closure() {
        let mut env = GlobalEnv::new();

        eval_str("(((lambda (x) (lambda (y) y)) 1) 2)", &mut env).should_ok(2.into());
        eval_str("(((lambda (x) (lambda (y) x)) 1) 2)", &mut env).should_ok(1.into());
    }
}
