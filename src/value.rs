use crate::eval::Ast;
use crate::eval::EvalError;
use crate::eval::Result;
use crate::local_env::LocalEnv;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Int(i32),
    Sym(Rc<str>),
    Nil,
    Cons(Rc<Value>, Rc<Value>),
    Ref(Rc<RefValue>),
}

// TODO: enum ValueRef { Box, Rc }

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RefValue {
    Lambda {
        param_names: Vec<Rc<str>>,
        rest_name: Option<Rc<str>>,
        body: Rc<[Ast]>,
        env: Option<Rc<LocalEnv>>,
    },
    Fun {
        name: String,
        fun: Fun,
    },
}

#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct Fun(pub Rc<dyn for<'a> Fn(&'a [Value]) -> Result>);

impl PartialEq for Fun {
    fn eq(&self, rhs: &Self) -> bool {
        let pl = self.0.as_ref() as *const _ as *const ();
        let pr = rhs.0.as_ref() as *const _ as *const ();
        pl == pr
    }
}
impl Eq for Fun {}
impl std::fmt::Debug for Fun {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        fmt.write_str("<primitive function>")
    }
}

impl Value {
    pub fn int(n: i32) -> Value {
        Value::Int(n)
    }
    pub fn bool(v: bool) -> Value {
        Value::Bool(v)
    }
    pub fn nil() -> Value {
        Value::Nil
    }
    pub fn cons<T1: Into<Value>, T2: Into<Value>>(car: T1, cdr: T2) -> Value {
        Value::Cons(Rc::new(car.into()), Rc::new(cdr.into()))
    }
    pub fn sym(name: &str) -> Value {
        Value::Sym(Rc::from(name))
    }
    pub fn fun<F>(name: &str, f: F) -> Value
    where
        F: for<'a> Fn(&'a [Value]) -> Result + 'static,
    {
        Value::Ref(Rc::new(RefValue::Fun {
            name: name.to_string(),
            fun: Fun(Rc::new(f)),
        }))
    }
    pub fn ref_value(v: RefValue) -> Value {
        Value::Ref(Rc::new(v))
    }
    pub fn lambda(
        param_names: Vec<Rc<str>>,
        rest_name: Option<Rc<str>>,
        body: Rc<[Ast]>,
        env: Option<Rc<LocalEnv>>,
    ) -> Value {
        Value::ref_value(RefValue::Lambda {
            param_names,
            rest_name,
            body,
            env,
        })
    }
    pub fn is_nil(&self) -> bool {
        self == &Value::Nil
    }
    pub fn to_vec(&self) -> Option<Vec<Rc<Value>>> {
        // TODO: refactor to use collect_improper()
        if self.is_nil() {
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
    pub fn collect_improper<'a, F, T, E>(
        &'a self,
        f: F,
    ) -> std::result::Result<(Vec<T>, Option<T>), E>
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
    pub fn fun0<F, R>(name: &str, f: F) -> Value
    where
        F: Fn() -> R + 'static,
        R: Into<Value>,
    {
        let fun = move |args: &[Value]| {
            if !args.is_empty() {
                Err(EvalError::ArgumentSize)
            } else {
                let v = f();
                Ok(v.into())
            }
        };
        Value::fun(name, fun)
    }
    pub fn fun1<F, T1, R>(name: &str, f: F) -> Value
    where
        F: Fn(T1) -> R + 'static,
        T1: Extract,
        R: Into<Value>,
    {
        let fun = move |args: &[Value]| {
            if args.len() != 1 {
                return Err(EvalError::ArgumentSize);
            }
            let x1 = T1::extract(&args[0]).ok_or(EvalError::InvalidArg)?;
            let v = f(x1).into();
            Ok(v)
        };
        Value::fun(name, fun)
    }
    pub fn fun2<F, T1, T2, R>(name: &str, f: F) -> Value
    where
        F: Fn(T1, T2) -> R + 'static,
        T1: Extract,
        T2: Extract,
        R: Into<Value>,
    {
        let fun = move |args: &[Value]| {
            if args.len() != 2 {
                return Err(EvalError::ArgumentSize);
            }
            let x1 = T1::extract(&args[0]).ok_or(EvalError::InvalidArg)?;
            let x2 = T2::extract(&args[1]).ok_or(EvalError::InvalidArg)?;
            let v = f(x1, x2).into();
            Ok(v)
        };
        Value::fun(name, fun)
    }
    pub fn fun_fold<F, T1>(name: &str, init: T1, f: F) -> Value
    where
        F: Fn(T1, T1) -> T1 + 'static,
        T1: Extract + Clone + Into<Value> + 'static,
    {
        let fun = move |args: &[Value]| {
            let mut a = init.clone();
            for x in args.iter() {
                match T1::extract(x) {
                    Some(x) => a = f(a, x),
                    None => return Err(EvalError::InvalidArg),
                }
            }
            Ok(a.into())
        };
        Value::fun(name, fun)
    }
    pub fn fun_reduce<F, T1>(name: &str, f: F) -> Value
    where
        F: Fn(T1, T1) -> T1 + 'static,
        T1: Extract + Clone + Into<Value> + 'static,
    {
        let fun = move |args: &[Value]| {
            let mut it = args.iter();
            let a = it.next().ok_or(EvalError::ArgumentSize)?;
            let mut a = T1::extract(a).ok_or(EvalError::InvalidArg)?;
            for x in it {
                match T1::extract(x) {
                    Some(x) => a = f(a, x),
                    None => return Err(EvalError::InvalidArg),
                }
            }
            Ok(a.into())
        };
        Value::fun(name, fun)
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

impl ToValue for bool {
    fn to_value(self) -> Value {
        Value::Bool(self)
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

impl ToValue for &[Rc<Value>] {
    fn to_value(self) -> Value {
        self.iter()
            .rev()
            .fold(Value::Nil, |a, x| Value::Cons(x.clone(), Rc::new(a)))
    }
}

impl ToValue for &[Value] {
    fn to_value(self) -> Value {
        self.iter().rev().fold(Value::Nil, |a, x| {
            Value::Cons(Rc::new(x.clone()), Rc::new(a))
        })
    }
}

pub trait Extract
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

impl Extract for bool {
    fn extract(x: &Value) -> Option<Self> {
        match x {
            Value::Bool(v) => Some(*v),
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
