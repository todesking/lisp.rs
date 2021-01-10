use crate::parser::Expr;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub enum EvalError {
    VariableNotFound(String),
    ImproperArgs,
    ArgumentSize,
    SymbolRequired,
    InvalidArg,
    CantApply(Rc<Value>),
}

// TODO: Regroup to SExpr { Value(SValue), Ref(Rc<SRef>) }
// SValue { Int(i32), ... }
// SRef { Cons(SExpr, Sexpr), Lambda(...), ... }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(i32),
    Sym(String),
    Nil,
    Cons(Rc<Value>, Rc<Value>),
    Lambda(
        Vec<String>,
        Option<String>,
        Vec<Rc<Value>>,
        Option<Rc<LocalEnv>>,
    ),
    Fun(FunData),
}

#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct FunData {
    name: String,
    fun: Rc<dyn for<'a> Fn(&'a [Rc<Value>]) -> Result>,
}

impl PartialEq for FunData {
    fn eq(&self, rhs: &Self) -> bool {
        let pl = self.fun.as_ref() as *const _ as *const ();
        let pr = rhs.fun.as_ref() as *const _ as *const ();
        self.name == rhs.name && pl == pr
    }
}
impl Eq for FunData {}
impl std::fmt::Debug for FunData {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        fmt.debug_struct("")
            .field("name", &self.name)
            .field("fun", &"<function>")
            .finish()
    }
}

impl Value {
    fn cons<T1: Into<Value>, T2: Into<Value>>(car: T1, cdr: T2) -> Value {
        Value::Cons(Rc::new(car.into()), Rc::new(cdr.into()))
    }
    fn to_vec(&self) -> Option<Vec<Rc<Value>>> {
        // TODO: refactor to use collect_improper()
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
    fn collect_improper<'a, F, T, E>(&'a self, f: F) -> std::result::Result<(Vec<T>, Option<T>), E>
    where
        F: Fn(&'a Value) -> std::result::Result<T, E>,
        T: 'a,
    {
        if self == &Value::Nil {
            return Ok((vec![], None));
        }

        let mut rest = self;
        let mut values = Vec::new();
        while let Value::Cons(car, cdr) = rest {
            rest = cdr;
            let v = f(car)?;
            values.push(v);
        }
        match rest {
            Value::Nil => Ok((values, None)),
            x => {
                let v = f(x)?;
                Ok((values, Some(v)))
            }
        }
    }
    // TODO: Use macro to abstract funX functions
    fn fun0<F, R>(name: &str, f: F) -> Value
    where
        F: Fn() -> R + 'static,
        R: Into<Value>,
    {
        let name = name.to_string();
        let fun = Rc::new(move |args: &[Rc<Value>]| {
            if !args.is_empty() {
                Err(EvalError::ArgumentSize)
            } else {
                let v = f();
                Ok(Rc::new(v.into()))
            }
        });
        Value::Fun(FunData { name, fun })
    }

    fn fun1<F, T1, R>(name: &str, f: F) -> Value
    where
        F: Fn(T1) -> R + 'static,
        T1: Extract,
        R: Into<Value>,
    {
        let name = name.to_string();
        let fun = Rc::new(move |args: &[Rc<Value>]| {
            if args.len() != 1 {
                return Err(EvalError::ArgumentSize);
            }
            let x1 = T1::extract(args[0].as_ref()).ok_or(EvalError::InvalidArg)?;
            let v = f(x1).into();
            Ok(Rc::new(v))
        });
        Value::Fun(FunData { name, fun })
    }
    fn fun2<F, T1, T2, R>(name: &str, f: F) -> Value
    where
        F: Fn(T1, T2) -> R + 'static,
        T1: Extract,
        T2: Extract,
        R: Into<Value>,
    {
        let name = name.to_string();
        let fun = Rc::new(move |args: &[Rc<Value>]| {
            if args.len() != 2 {
                return Err(EvalError::ArgumentSize);
            }
            let x1 = T1::extract(args[0].as_ref()).ok_or(EvalError::InvalidArg)?;
            let x2 = T2::extract(args[1].as_ref()).ok_or(EvalError::InvalidArg)?;
            let v = f(x1, x2).into();
            Ok(Rc::new(v))
        });
        Value::Fun(FunData { name, fun })
    }
    fn fun_fold<F, T1>(name: &str, init: T1, f: F) -> Value
    where
        F: Fn(T1, T1) -> T1 + 'static,
        T1: Extract + Clone + Into<Value> + 'static,
    {
        let name = name.to_string();
        let fun = Rc::new(move |args: &[Rc<Value>]| {
            let mut a = init.clone();
            for x in args.iter() {
                match T1::extract(x) {
                    Some(x) => a = f(a, x),
                    None => return Err(EvalError::InvalidArg),
                }
            }
            Ok(Rc::new(a.into()))
        });
        Value::Fun(FunData { name, fun })
    }
    fn fun_reduce<F, T1>(name: &str, f: F) -> Value
    where
        F: Fn(T1, T1) -> T1 + 'static,
        T1: Extract + Clone + Into<Value> + 'static,
    {
        let name = name.to_string();
        let fun = Rc::new(move |args: &[Rc<Value>]| {
            let mut it = args.iter();
            let a = it.next().ok_or(EvalError::ArgumentSize)?;
            let a = T1::extract(a).ok_or(EvalError::InvalidArg)?;
            let mut a = a;
            for x in it {
                match T1::extract(x) {
                    Some(x) => a = f(a, x),
                    None => return Err(EvalError::InvalidArg),
                }
            }
            Ok(Rc::new(a.into()))
        });
        Value::Fun(FunData { name, fun })
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

impl ToValue for &[Rc<Value>] {
    fn to_value(self) -> Value {
        self.iter()
            .rev()
            .fold(Value::Nil, |a, x| Value::Cons(x.clone(), Rc::new(a)))
    }
}

trait Extract
where
    Self: Sized,
{
    fn extract(x: &Value) -> Option<Self>;
}

impl Extract for i32 {
    fn extract(x: &Value) -> Option<Self> {
        match x {
            Value::Int(n) => Some(*n),
            _ => None,
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
    fn new(
        param_names: &[String],
        rest_name: Option<String>,
        args: &[Rc<Value>],
        parent: Option<Rc<LocalEnv>>,
    ) -> std::result::Result<LocalEnv, EvalError> {
        let invalid_argument_size = (rest_name.is_none() && param_names.len() != args.len())
            || (rest_name.is_some() && param_names.len() > args.len());
        if invalid_argument_size {
            Err(EvalError::ArgumentSize)
        } else {
            let mut values = std::collections::HashMap::new();
            for (k, v) in param_names.iter().zip(args) {
                values.insert(k.clone(), v.clone());
            }
            if let Some(rest_name) = rest_name {
                values.insert(rest_name, Rc::new(Value::from(&args[param_names.len()..])));
            }

            Ok(LocalEnv { values, parent })
        }
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
        Value::Lambda(_, _, _, _) => unimplemented!(),
        Value::Fun(_) => unimplemented!(),
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
                            let value = eval_local(value, global, local)?;
                            global.set(name, value);
                            Ok(Rc::new(Value::Nil))
                        }
                        _ => Err(EvalError::SymbolRequired),
                    },
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            Value::Sym(name) if name == "lambda" => match cdr.as_ref() {
                Value::Cons(params, body) => {
                    let (param_names, rest_name) = params.collect_improper(|v| match v {
                        Value::Sym(name) => Ok(name),
                        _ => Err(EvalError::SymbolRequired),
                    })?;
                    match body.to_vec() {
                        None => Err(EvalError::ImproperArgs),
                        Some(body) => match body.as_slice() {
                            [] => Err(EvalError::ArgumentSize),
                            body => eval_lambda(&param_names, rest_name, body, local),
                        },
                    }
                }
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
    rest_name: Option<&String>,
    body: &[Rc<Value>],
    local: Option<&Rc<LocalEnv>>,
) -> Result {
    let param_names: Vec<String> = param_names.iter().map(|x| (*x).clone()).collect();
    let body: Vec<Rc<Value>> = body.to_vec();
    Ok(Rc::new(Value::Lambda(
        param_names,
        rest_name.cloned(),
        body,
        local.cloned(),
    )))
}

fn eval_apply(f: &Rc<Value>, args: &[Rc<Value>], global: &mut GlobalEnv) -> Result {
    match f.as_ref() {
        Value::Lambda(param_names, rest_name, body, parent) => {
            let local = LocalEnv::new(param_names, rest_name.clone(), args, parent.clone())?;
            let local = Rc::new(local);
            let mut e = Rc::new(Value::Nil);
            for b in body {
                e = eval_local(b, global, Some(&local))?;
            }
            Ok(e)
        }
        Value::Fun(FunData { fun, .. }) => fun(args),
        _ => Err(EvalError::CantApply(f.clone())),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::Expr;

    fn eval_str(s: &str, env: &mut GlobalEnv) -> Result {
        let expr = s.parse::<Expr>().expect("should valid sexpr");
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

        eval_str("(define x '1)", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1.into());

        eval_str("(define x 2 3)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(define 1 2)", &mut env).should_error(EvalError::SymbolRequired);
        eval_str("(define x aaa)", &mut env)
            .should_error(EvalError::VariableNotFound("aaa".into()));
    }

    #[test]
    fn test_lambda_error() {
        let mut env = GlobalEnv::new();

        eval_str("(lambda)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(lambda () 1 . 2)", &mut env).should_error(EvalError::ImproperArgs);
        eval_str("(lambda (x))", &mut env).should_error(EvalError::ArgumentSize);

        eval_str("(lambda 1 1)", &mut env).should_error(EvalError::SymbolRequired);
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

    #[test]
    fn test_lambda_varargs() {
        let mut env = GlobalEnv::new();

        eval_str("(define my-list (lambda x x))", &mut env).should_ok(Value::Nil);
        eval_str("(my-list 1 2 3)", &mut env).should_ok(list!(1, 2, 3));
        eval_str("(my-list)", &mut env).should_ok(list!());

        eval_str("(define my-head (lambda (x . xs) x))", &mut env).should_ok(Value::Nil);
        eval_str("(define my-tail (lambda (x . xs) xs))", &mut env).should_ok(Value::Nil);
        eval_str("(my-head 1)", &mut env).should_ok(1.into());
        eval_str("(my-tail 1)", &mut env).should_ok(list!());
        eval_str("(my-head 1 2)", &mut env).should_ok(1.into());
        eval_str("(my-tail 1 2)", &mut env).should_ok(list!(2));
        eval_str("(my-head)", &mut env).should_error(EvalError::ArgumentSize);
    }

    #[test]
    fn test_fun() {
        let mut env = GlobalEnv::new();

        env.set("f0", Rc::new(Value::fun0("f0", || 123)));
        eval_str("(f0)", &mut env).should_ok(123.into());
        eval_str("(f0 1)", &mut env).should_error(EvalError::ArgumentSize);

        env.set("f1", Rc::new(Value::fun1("f1", |n: i32| n)));
        eval_str("(f1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f1 1 2)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f1 1)", &mut env).should_ok(1.into());

        env.set("f2", Rc::new(Value::fun2("f2", |n: i32, m: i32| n + m)));
        eval_str("(f2)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1 2 3)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f2 1 2)", &mut env).should_ok(3.into());

        env.set("sum", Rc::new(Value::fun_fold("sum", 0, |a, x| a + x)));
        eval_str("(sum)", &mut env).should_ok(0.into());
        eval_str("(sum 1)", &mut env).should_ok(1.into());
        eval_str("(sum 1 2)", &mut env).should_ok(3.into());
        eval_str("(sum 'x)", &mut env).should_error(EvalError::InvalidArg);

        env.set(
            "sum1",
            Rc::new(Value::fun_reduce("sum1", |a: i32, x: i32| a + x)),
        );
        eval_str("(sum1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(sum1 'x)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(sum1 1)", &mut env).should_ok(1.into());
        eval_str("(sum1 1 2)", &mut env).should_ok(3.into());
    }
}
